#include "base.h"
#include "log.h"
#include "buffer.h"
#include "response.h"

#include "plugin.h"

#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define PAK_MAXFILES	4096

#define PAK_SIZEHEADER	12
#define PAK_SIZEDIRITEM 64

#define PAK_IDENT		(('K'<<24)+('C'<<16)+('A'<<8)+'P')

#define ZIP_MAXFILES	0x8000

#define ZIP_BUFREADCOMMENT		1024
#define ZIP_SIZELOCALHEADER		30
#define ZIP_SIZECENTRALHEADER	20
#define ZIP_SIZECENTRALDIRITEM	46

#define ZIP_LOCALHEADERMAGIC	0x04034b50
#define ZIP_CENTRALHEADERMAGIC	0x02014b50
#define ZIP_ENDHEADERMAGIC		0x06054b50

#ifndef Z_DEFLATED
#define Z_DEFLATED 8
#endif

#define LE32(p) (((unsigned)(p)[3]<<24)|((p)[2]<<16)|((p)[1]<<8)|(p)[0])
#define LE16(p) (((p)[1]<<8)|(p)[0])

/* request: accept-encoding */
#define HTTP_ACCEPT_ENCODING_IDENTITY BV(0)
#define HTTP_ACCEPT_ENCODING_GZIP	  BV(1)
#define HTTP_ACCEPT_ENCODING_DEFLATE  BV(2)

typedef struct packfile_s {
	struct packfile_s *next; /* hash table entry */
	char		*name;
	size_t		namelen;
	size_t		filepos;
	size_t		filelen;	/* uncompressed length */
	unsigned	filecrc;
	size_t		complen;
	unsigned	compmtd;	/* compression method, 0 (stored) or Z_DEFLATED */
	int			coherent;	/* 1 if local file header has been checked */
} packfile;

typedef struct packdir_s {
	struct packdir_s *next; /* cache entry */
	unsigned	num_files;
	packfile	*files;
	packfile	**file_hash;
	unsigned	hash_size;
	char		*names;
	buffer		*filename;
	time_t		mtime;
} packdir;

typedef struct packsearch_s {
	struct packsearch_s *next;
	packdir *pack;
} packsearch;

/* plugin config for all request/connections */

typedef struct {
	packsearch *search;
	buffer *content;
	int strip;
	buffer *referer;
} plugin_config;

typedef struct {
	PLUGIN_DATA;

	plugin_config **config_storage;

	plugin_config conf;

	packdir *cache;
} plugin_data;

/* init the plugin data */
INIT_FUNC(mod_pak_init) {
	plugin_data *p;

	p = calloc(1, sizeof(*p));

	return p;
}

static void free_search_path(plugin_config *s) {
	packsearch *search, *next;

	for (search = s->search; search; search = next) {
		next = search->next;
		free(search);
	}
}

static void free_pack_cache(plugin_data *p) {
	packdir *pack, *next;

	for (pack = p->cache; pack; pack = next) {
		next = pack->next;
		buffer_free(pack->filename);
		free(pack);
	}
}

/* detroy the plugin data */
FREE_FUNC(mod_pak_free) {
	plugin_data *p = p_d;

	UNUSED(srv);

	if (!p) return HANDLER_GO_ON;

	if (p->config_storage) {
		size_t i;

		for (i = 0; i < srv->config_context->used; i++) {
			plugin_config *s = p->config_storage[i];

			if (!s) continue;

			free_search_path(s);
			buffer_free(s->content);
			free(s);
		}
		free(p->config_storage);
	}

	free_pack_cache(p);
	free(p);

	return HANDLER_GO_ON;
}

/* hashes quake path in a case insensitive way */
static unsigned caseless_hash_path(const char *s, unsigned size) {
	unsigned hash, c;

	hash = 0;
	while (*s) {
		c = *s++;
		if (c >= 'A' && c <= 'Z')
			c += ('a' - 'A');
		hash = 127 * hash + c;
	}

	hash = (hash >> 20) ^(hash >> 10) ^ hash;
	return hash & (size - 1);
}

static unsigned npot32(unsigned k) {
	if (k == 0)
		return 1;

	k--;
	k = k | (k >> 1);
	k = k | (k >> 2);
	k = k | (k >> 4);
	k = k | (k >> 8);
	k = k | (k >> 16);

	return k + 1;
}

/* allocates packdir instance along with filenames and hashes in one chunk of memory */
static packdir *pack_alloc(unsigned num_files, size_t names_len) {
	packdir *pack;
	unsigned hash_size;

	hash_size = npot32(num_files / 3);

	pack = malloc(sizeof(packdir) +
	              num_files * sizeof(packfile) +
	              hash_size * sizeof(packfile *) +
	              names_len);
	pack->num_files = num_files;
	pack->hash_size = hash_size;
	pack->files = (packfile *)(pack + 1);
	pack->file_hash = (packfile **)(pack->files + num_files);
	pack->names = (char *)(pack->file_hash + hash_size);
	memset(pack->file_hash, 0, hash_size * sizeof(packfile *));

	return pack;
}

static void pack_hash_file(packdir *pack, packfile *file) {
	unsigned hash = caseless_hash_path(file->name, pack->hash_size);

	file->next = pack->file_hash[hash];
	pack->file_hash[hash] = file;
}

static size_t get_pak_info(FILE *fp, packfile *file, size_t *len, size_t remaining) {
	size_t file_len, file_pos, name_size;
	unsigned char header[PAK_SIZEDIRITEM], *p;

	if (fread(&header, 1, sizeof(header), fp) != sizeof(header))
		return 0;

	file_pos = LE32(&header[PAK_SIZEDIRITEM - 8]);
	file_len = LE32(&header[PAK_SIZEDIRITEM - 4]);
	if (file_len > LONG_MAX)
		return 0;
	if (file_pos > LONG_MAX - file_len)
		return 0;

	p = memchr(header, 0, PAK_SIZEDIRITEM - 8);
	if (!p)
		return 0; /* for paks it is illegal to have no terminating NUL */

	name_size = p - header;

	/* fill in the info */
	if (file) {
		if (name_size >= remaining)
			return 0; /* directory changed on disk? */
		file->compmtd = 0;
		file->complen = file_len;
		file->filelen = file_len;
		file->filepos = file_pos;
		file->filecrc = 0;
		memcpy(file->name, header, name_size);
		file->name[name_size] = 0;
	}

	*len = name_size + 1;

	return PAK_SIZEDIRITEM;
}

static packdir *load_pak_file(FILE *fp, unsigned char *header) {
	packfile		*file;
	size_t			dir_ofs, dir_len;
	unsigned		i, num_files;
	char			*name;
	size_t			len, names_len;
	packdir			*pack;

	/* ident has already been checked */
	dir_ofs = LE32(&header[4]);
	dir_len = LE32(&header[8]);
	if (dir_len > LONG_MAX || dir_len % PAK_SIZEDIRITEM)
		return NULL;

	num_files = dir_len / PAK_SIZEDIRITEM;
	if (num_files < 1)
		return NULL;
	if (num_files > PAK_MAXFILES)
		return NULL;

	if (dir_ofs > LONG_MAX - dir_len)
		return NULL;

	/* parse the directory */
	if (fseek(fp, (long)dir_ofs, SEEK_SET))
		return NULL;
	names_len = 0;
	for (i = 0; i < num_files; i++) {
		if (!get_pak_info(fp, NULL, &len, 0))
			return NULL;
		names_len += len;
	}

	/* allocate the pack */
	pack = pack_alloc(num_files, names_len);

	/* parse the directory */
	if (fseek(fp, (long)dir_ofs, SEEK_SET))
		return NULL;
	file = pack->files;
	name = pack->names;
	for (i = 0; i < pack->num_files; i++) {
		file->name = name;
		if (!get_pak_info(fp, file, &len, names_len))
			goto fail; /* directory changed on disk? */

		file->namelen = len - 1;
		file->coherent = 1;

		pack_hash_file(pack, file);

		/* advance pointers, decrement counters */
		file++;

		name += len;
		names_len -= len;
	}

	return pack;

fail:
	free(pack);
	return NULL;
}

/* locate the central directory of a zipfile (at the end, just before the global comment) */
static size_t search_central_header(FILE *fp) {
	size_t file_size, back_read;
	size_t max_back = 0xffff; /* maximum size of global comment */
	unsigned char buf[ZIP_BUFREADCOMMENT + 4];
	long ret;

	if (fseek(fp, 0, SEEK_END) == -1)
		return 0;

	ret = ftell(fp);
	if (ret == -1)
		return 0;
	file_size = (size_t)ret;
	if (max_back > file_size)
		max_back = file_size;

	back_read = 4;
	while (back_read < max_back) {
		size_t i, read_size, read_pos;

		if (back_read + ZIP_BUFREADCOMMENT > max_back)
			back_read = max_back;
		else
			back_read += ZIP_BUFREADCOMMENT;

		read_pos = file_size - back_read;

		read_size = back_read;
		if (read_size > ZIP_BUFREADCOMMENT + 4)
			read_size = ZIP_BUFREADCOMMENT + 4;

		if (fseek(fp, (long)read_pos, SEEK_SET) == -1)
			break;
		if (fread(buf, 1, read_size, fp) != read_size)
			break;

		i = read_size - 4;
		do {
			/* check the magic */
			if (LE32(buf + i) == ZIP_ENDHEADERMAGIC)
				return read_pos + i;
		} while (i--);
	}

	return 0;
}

/* get info about the current file in the zipfile, with internal only info */
static size_t get_zip_info(FILE *fp, size_t pos, packfile *file, size_t *len, size_t remaining) {
	size_t name_size, xtra_size, comm_size;
	size_t comp_len, file_len, file_pos;
	unsigned comp_mtd, file_crc;
	unsigned char header[ZIP_SIZECENTRALDIRITEM]; /* we can't use a struct here because of packing */

	*len = 0;

	if (pos > LONG_MAX)
		return 0;
	if (fseek(fp, (long)pos, SEEK_SET) == -1)
		return 0;
	if (fread(header, 1, sizeof(header), fp) != sizeof(header))
		return 0;

	/* check the magic */
	if (LE32(&header[0]) != ZIP_CENTRALHEADERMAGIC)
		return 0;

	comp_mtd = LE16(&header[10]);
	file_crc = LE32(&header[16]);
	comp_len = LE32(&header[20]);
	file_len = LE32(&header[24]);
	name_size = LE16(&header[28]);
	xtra_size = LE16(&header[30]);
	comm_size = LE16(&header[32]);
	file_pos = LE32(&header[42]);

	if (file_len > LONG_MAX)
		return 0;
	if (comp_len > LONG_MAX || file_pos > LONG_MAX - comp_len)
		return 0;

	if (!file_len || !comp_len)
		goto skip; /* skip directories and empty files */
	if (!comp_mtd) {
		if (file_len != comp_len)
			goto skip;
	} else if (comp_mtd != Z_DEFLATED) {
		goto skip;
	}
	if (!name_size)
		goto skip;
	if (name_size >= 1024)
		goto skip;

	/* fill in the info */
	if (file) {
		if (name_size >= remaining)
			return 0; /* directory changed on disk? */
		file->compmtd = comp_mtd;
		file->complen = comp_len;
		file->filelen = file_len;
		file->filepos = file_pos;
		file->filecrc = file_crc;
		if (fread(file->name, 1, name_size, fp) != name_size)
			return 0;
		file->name[name_size] = 0;
	}

	*len = name_size + 1;

skip:
	return ZIP_SIZECENTRALDIRITEM + name_size + xtra_size + comm_size;
}

static packdir *load_zip_file(FILE *fp) {
	packfile		*file;
	char			*name;
	size_t			len, names_len;
	unsigned		i, num_disk, num_disk_cd, num_files, num_files_cd;
	size_t			header_pos, central_ofs, central_size, central_end;
	size_t			extra_bytes, ofs;
	packdir			*pack;
	unsigned char	header[ZIP_SIZECENTRALHEADER];

	header_pos = search_central_header(fp);
	if (!header_pos)
		return NULL;
	if (fseek(fp, (long)header_pos, SEEK_SET) == -1)
		return NULL;
	if (fread(header, 1, sizeof(header), fp) != sizeof(header))
		return NULL;

	num_disk = LE16(&header[4]);
	num_disk_cd = LE16(&header[6]);
	num_files = LE16(&header[8]);
	num_files_cd = LE16(&header[10]);
	if (num_files_cd != num_files || num_disk_cd != 0 || num_disk != 0)
		return NULL;
	if (num_files < 1)
		return NULL;
	if (num_files > ZIP_MAXFILES)
		return NULL;

	central_size = LE32(&header[12]);
	central_ofs = LE32(&header[16]);
	central_end = central_ofs + central_size;
	if (central_end > header_pos || central_end < central_ofs)
		return NULL;

	/* non-zero for sfx? */
	extra_bytes = header_pos - central_end;

	/* parse the directory */
	num_files = 0;
	names_len = 0;
	header_pos = central_ofs + extra_bytes;
	for (i = 0; i < num_files_cd; i++) {
		ofs = get_zip_info(fp, header_pos, NULL, &len, 0);
		if (!ofs)
			return NULL;
		header_pos += ofs;

		if (len) {
			names_len += len;
			num_files++;
		}
	}

	if (!num_files)
		return NULL;

	/* allocate the pack */
	pack = pack_alloc(num_files, names_len);

	/* parse the directory */
	file = pack->files;
	name = pack->names;
	header_pos = central_ofs + extra_bytes;
	for (i = 0; i < num_files_cd; i++) {
		if (!num_files)
			break;
		file->name = name;
		ofs = get_zip_info(fp, header_pos, file, &len, names_len);
		if (!ofs)
			goto fail; /* directory changed on disk? */
		header_pos += ofs;

		if (len) {
			/* fix absolute position */
			file->filepos += extra_bytes;

			file->namelen = len - 1;
			file->coherent = 0;

			pack_hash_file(pack, file);

			/* advance pointers, decrement counters */
			file++;
			num_files--;

			name += len;
			names_len -= len;
		}
	}

	return pack;

fail:
	free(pack);
	return NULL;
}

static packdir *try_load_pack(buffer *fn) {
	unsigned char header[PAK_SIZEHEADER];
	packdir *pack;
	FILE *fp;

	fp = fopen(fn->ptr, "rb");
	if (!fp) {
		return NULL;
	}

	/* read header */
	if (fread(header, 1, sizeof(header), fp) != sizeof(header)) {
		goto fail;
	}

	if (LE32(&header[0]) == PAK_IDENT) {
		/* this is a pak file */
		pack = load_pak_file(fp, header);
	} else {
		/* may be a zip file */
		pack = load_zip_file(fp);
	}

	fclose(fp);

	if (pack) {
		pack->filename = buffer_init_buffer(fn);
		pack->mtime = 0; /* TODO */
	}

	return pack;

fail:
	fclose(fp);
	return NULL;
}

/* packfiles are kept in global cache to avoid wasting memory */
/* the same file can be referenced multiple times in server config contexts */
static packdir *try_add_pack(server *srv, plugin_data *p, buffer *fn) {
	packdir *pack;

	/* check if this pack is already loaded */
	for (pack = p->cache; pack; pack = pack->next) {
		if (!strcmp(pack->filename->ptr, fn->ptr)) {
			return pack;
		}
	}

	/* load it and add into the cache */
	pack = try_load_pack(fn);
	if (pack) {
		pack->next = p->cache;
		p->cache = pack;
		log_error_write(srv, __FILE__, __LINE__, "sbsd",
		                "loaded packfile", fn, "hashtable", pack->hash_size);
	} else {
		log_error_write(srv, __FILE__, __LINE__, "sb",
		                "failed to load packfile", fn);
	}

	return pack;
}


/* handle plugin config and check values */

SETDEFAULTS_FUNC(mod_pak_set_defaults) {
	plugin_data *p = p_d;
	size_t i;

	config_values_t cv[] = {
		{ "pak.search", NULL, T_CONFIG_ARRAY, T_CONFIG_SCOPE_CONNECTION },		/* 0 */
		{ "pak.content", NULL, T_CONFIG_STRING, T_CONFIG_SCOPE_CONNECTION },	/* 1 */
		{ "pak.strip", NULL, T_CONFIG_INT, T_CONFIG_SCOPE_CONNECTION },			/* 2 */
		{ "pak.referer", NULL, T_CONFIG_STRING, T_CONFIG_SCOPE_CONNECTION },	/* 3 */
		{ NULL, NULL, T_CONFIG_UNSET, T_CONFIG_SCOPE_UNSET }
	};

	if (!p) return HANDLER_ERROR;

	p->config_storage = calloc(1, srv->config_context->used * sizeof(specific_config *));

	for (i = 0; i < srv->config_context->used; i++) {
		data_config const* config = (data_config const*)srv->config_context->data[i];
		plugin_config *s = calloc(1, sizeof(plugin_config));
		array *paklist = array_init();

		s->content = buffer_init_string("application/octet-stream");
		s->strip = 1;
		s->referer = buffer_init();

		cv[0].destination = paklist;
		cv[1].destination = s->content;
		cv[2].destination = &s->strip;
		cv[3].destination = s->referer;

		p->config_storage[i] = s;

		if (0 != config_insert_values_global(srv, config->value, cv, i == 0 ? T_CONFIG_SCOPE_SERVER : T_CONFIG_SCOPE_CONNECTION)) {
			return HANDLER_ERROR;
		}

		if (paklist->used) {
			size_t j;
			for (j = 0; j < paklist->used; j++) {
				data_string *ds = (data_string *)paklist->data[j];
				packdir *pack = try_add_pack(srv, p, ds->value);
				if (pack) {
					packsearch *search = calloc(1, sizeof(packsearch));
					search->pack = pack;
					search->next = s->search;
					s->search = search;
				}
			}
		}

		array_free(paklist);
	}

	return HANDLER_GO_ON;
}

#define PATCH(x) \
	p->conf.x = s->x;
static int mod_pak_patch_connection(server *srv, connection *con, plugin_data *p) {
	size_t i, j;
	plugin_config *s = p->config_storage[0];

	PATCH(search);
	PATCH(content);
	PATCH(strip);
	PATCH(referer);

	/* skip the first, the global context */
	for (i = 1; i < srv->config_context->used; i++) {
		data_config *dc = (data_config *)srv->config_context->data[i];
		s = p->config_storage[i];

		/* condition didn't match */
		if (!config_check_cond(srv, con, dc)) continue;

		/* merge config */
		for (j = 0; j < dc->value->used; j++) {
			data_unset *du = dc->value->data[j];

			if (buffer_is_equal_string(du->key, CONST_STR_LEN("pak.search"))) {
				PATCH(search);
			}
			if (buffer_is_equal_string(du->key, CONST_STR_LEN("pak.content"))) {
				PATCH(content);
			}
			if (buffer_is_equal_string(du->key, CONST_STR_LEN("pak.strip"))) {
				PATCH(strip);
			}
			if (buffer_is_equal_string(du->key, CONST_STR_LEN("pak.referer"))) {
				PATCH(referer);
			}
		}
	}

	return 0;
}
#undef PATCH

static int check_header_coherency(packdir *pack, packfile *entry) {
	unsigned flags, comp_mtd, file_crc;
	size_t comp_len, file_len;
	size_t name_size, xtra_size;
	unsigned char header[ZIP_SIZELOCALHEADER];
	size_t ofs;
	FILE *fp;

	/* reopen it */
	fp = fopen(pack->filename->ptr, "rb");
	if (!fp)
		return 0;

	if (fseek(fp, (long)entry->filepos, SEEK_SET) == -1)
		goto fail;
	if (fread(header, 1, sizeof(header), fp) != sizeof(header))
		goto fail;

	fclose(fp);

	/* check the magic */
	if (LE32(&header[0]) != ZIP_LOCALHEADERMAGIC)
		return 0;

	flags = LE16(&header[6]);
	comp_mtd = LE16(&header[8]);
	file_crc = LE32(&header[14]);
	comp_len = LE32(&header[18]);
	file_len = LE32(&header[22]);
	name_size = LE16(&header[26]);
	xtra_size = LE16(&header[28]);

	/* check compression method */
	if (comp_mtd != entry->compmtd)
		return 0;

	/* bit 3 tells that crc and file length were not known
	   at the time local header was written, don't check them */
	if ((flags & 8) == 0) {
		if (file_crc != entry->filecrc)
			return 0;
		if (comp_len != entry->complen)
			return 0;
		if (file_len != entry->filelen)
			return 0;
	}

	ofs = ZIP_SIZELOCALHEADER + name_size + xtra_size;
	if (entry->filepos > LONG_MAX - ofs) {
		return 0;
	}

	entry->filepos += ofs;
	entry->coherent = 1;
	return 1;

fail:
	fclose(fp);
	return 0;
}

/* search through the path, one element at a time */
static packfile *find_packfile(server *srv, connection *con, plugin_data *p, int encoding, packdir **pack_p) {
	packsearch	*search;
	packdir		*pack;
	packfile	*entry;
	const char	*name, *s;
	size_t		namelen;
	unsigned	hash;
	int			i;

	UNUSED(srv);

	/* strip some leading path components */
	name = con->uri.path->ptr;
	for (i = 0; i < p->conf.strip; i++) {
		s = strchr(name, '/');
		if (!s) {
			break;
		}
		name = s + 1;
	}

	if (!*name) {
		return NULL;
	}

	if (con->conf.log_request_handling) {
		log_error_write(srv, __FILE__, __LINE__, "ss", "searching for", name);
	}

	namelen = strlen(name);
	hash = caseless_hash_path(name, 0);
	for (search = p->conf.search; search; search = search->next) {
		/* look through all the pak file elements */
		pack = search->pack;
		entry = pack->file_hash[ hash & (pack->hash_size - 1) ];
		for (; entry; entry = entry->next) {
			if (entry->namelen != namelen) {
				continue;
			}
			if (entry->compmtd && !(encoding & HTTP_ACCEPT_ENCODING_GZIP)) {
				continue;
			}
			if (!buffer_caseless_compare(entry->name, entry->namelen, name, namelen)) {
				/* found it! */
				if (con->conf.log_request_handling) {
					log_error_write(srv, __FILE__, __LINE__, "sbs",
					                "found in", pack->filename, entry->compmtd ? "compressed" : "stored");
				}
				*pack_p = pack;
				return entry;
			}
		}
	}

	*pack_p = NULL;
	return NULL;
}

static void handle_stored(server *srv, connection *con, packdir *pack, packfile *entry) {
	UNUSED(srv);
	chunkqueue_append_file(con->write_queue, pack->filename, entry->filepos, entry->filelen);
}

static void handle_gzipped(server *srv, connection *con, packdir *pack, packfile *entry) {
	unsigned char c[10];

	UNUSED(srv);

	/* write gzip header */
	c[0] = 0x1f;
	c[1] = 0x8b;
	c[2] = Z_DEFLATED;
	c[3] = 0; /* options */
	c[4] = (pack->mtime >>	0) & 0xff;
	c[5] = (pack->mtime >>	8) & 0xff;
	c[6] = (pack->mtime >> 16) & 0xff;
	c[7] = (pack->mtime >> 24) & 0xff;
	c[8] = 0x00; /* extra flags */
	c[9] = 0x03; /* UNIX */
	chunkqueue_append_mem(con->write_queue, (char *)c, 10);

	/* write gzip body */
	chunkqueue_append_file(con->write_queue, pack->filename, entry->filepos, entry->complen);

	/* write gzip trailer */
	c[0] = (entry->filecrc >>  0) & 0xff;
	c[1] = (entry->filecrc >>  8) & 0xff;
	c[2] = (entry->filecrc >> 16) & 0xff;
	c[3] = (entry->filecrc >> 24) & 0xff;
	c[4] = (entry->filelen >>  0) & 0xff;
	c[5] = (entry->filelen >>  8) & 0xff;
	c[6] = (entry->filelen >> 16) & 0xff;
	c[7] = (entry->filelen >> 24) & 0xff;
	chunkqueue_append_mem(con->write_queue, (char *)c, 8);
}

URIHANDLER_FUNC(mod_pak_uri_handler) {
	plugin_data *p = p_d;
	data_string *ds;
	packdir *pack;
	packfile *entry;
	int encoding;

	if (con->mode != DIRECT || con->http_status) return HANDLER_GO_ON;

	if (con->request.http_method != HTTP_METHOD_GET &&
	    con->request.http_method != HTTP_METHOD_HEAD) return HANDLER_GO_ON;

	if (buffer_is_empty(con->uri.path)) return HANDLER_GO_ON;

	mod_pak_patch_connection(srv, con, p);

	encoding = 0;

	ds = (data_string *)array_get_element(con->request.headers, "Accept-Encoding");
	if (ds) {
		/*if (strstr (ds->value->ptr, "identity")) encoding |= HTTP_ACCEPT_ENCODING_IDENTITY;*/
		if (strstr(ds->value->ptr, "gzip")) encoding |= HTTP_ACCEPT_ENCODING_GZIP;
		/*if (strstr (ds->value->ptr, "deflate"))  encoding |= HTTP_ACCEPT_ENCODING_DEFLATE;*/
	}

	entry = find_packfile(srv, con, p, encoding, &pack);
	if (!entry) {
		/* not found */
		return HANDLER_GO_ON;
	}

	/* found */
	buffer_reset(con->uri.path);

	/* check referer */
	if (!buffer_is_empty(p->conf.referer)) {
		ds = (data_string *)array_get_element(con->request.headers, "Referer");
		if (!ds || ds->value->used < p->conf.referer->used ||
		    strncasecmp(ds->value->ptr, p->conf.referer->ptr, p->conf.referer->used - 1)) {
			con->http_status = 403;
			return HANDLER_FINISHED;
		}
	}

	if (!entry->coherent && !check_header_coherency(pack, entry)) {
		con->http_status = 500;
		log_error_write(srv, __FILE__, __LINE__, "s", "coherency check failed");
		return HANDLER_FINISHED;
	}

	chunkqueue_reset(con->write_queue);

	if (entry->compmtd) {
		handle_gzipped(srv, con, pack, entry);
	} else {
		handle_stored(srv, con, pack, entry);
	}

	con->file_finished = 1;
	con->file_started  = 1;

	con->http_status = 200;

	if (entry->compmtd) {
		response_header_overwrite(srv, con, CONST_STR_LEN("Content-Encoding"), CONST_STR_LEN("gzip"));
	}
	response_header_overwrite(srv, con, CONST_STR_LEN("Content-Type"), CONST_BUF_LEN(p->conf.content));

	return HANDLER_FINISHED;
}

/* this function is called at dlopen() time and inits the callbacks */

int mod_pak_plugin_init(plugin *p) {
	p->version	   = LIGHTTPD_VERSION_ID;
	p->name		   = buffer_init_string("pak");

	p->init		   = mod_pak_init;
	p->handle_uri_clean  = mod_pak_uri_handler;
	p->set_defaults  = mod_pak_set_defaults;
	p->cleanup	   = mod_pak_free;

	p->data		   = NULL;

	return 0;
}

