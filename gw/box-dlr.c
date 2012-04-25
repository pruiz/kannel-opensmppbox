/*
 * gw/box-dlr.c
 *
 * Implementation of handling of opensmppbox additions to delivery reports
 *  (DLRs)
 *
 * Aarno Syvanen <aarno@alisanus.com>
 */

#include <ctype.h>
#include <time.h>
#include <errno.h>
#include <limits.h>
#include <string.h>

#include <unistd.h>

#include "box-dlr.h"
#include "gw/dlr.h"
#include "gw/dlr_p.h"
#include "gwlib/dbpool.h"

/* Our connection pool. */
static DBPool *box_pool = NULL;

/*
 * This is the global list used by internal memory where all messages being sent
 * out are being kept track of his list is looked up once a delivery report comes in
 */
static List *box_dlr_waiting_list;
static RWLock rwlock;

typedef struct _box_dlr_entry {
    struct dlr_entry *entry;
    Octstr *id;
} box_dlr_entry;

/*
 * dlr-peek: Find and return box_dlr_entry, using msg id as key. 
 * If entry not found return NULL.
 * NOTE: Caller will destroy box_dlr_entry
 */
typedef struct _box_dlr_storage {
    const char *type;
    box_dlr_entry* (*dlr_peek) (const Octstr *id, int usesmpp);
    void (*dlr_add_with_id)(box_dlr_entry *entry);
    void (*dlr_add_mem_with_id)(box_dlr_entry *entry, Msg *msg);
    void (*dlr_shutdown) (void);
} box_dlr_storage;


typedef struct _box_dlr_db_fields {
    struct dlr_db_fields *dlr_db_fields;
    Octstr *field_id;
} box_dlr_db_fields;


static box_dlr_storage *handles = NULL;
static box_dlr_db_fields *box_fields = NULL;
 

static void box_dlr_storage_destroy(box_dlr_storage *handles);

static box_dlr_entry *box_dlr_entry_create(void);
static box_dlr_entry *box_dlr_entry_duplicate(const box_dlr_entry *dlr);
static void dlr_entry_dump(const box_dlr_entry *box_dlr);
static void box_dlr_entry_destroy(box_dlr_entry *box_dlr);

static void box_dlr_db_fields_destroy(box_dlr_db_fields *fields);
static box_dlr_db_fields *box_dlr_db_fields_create(CfgGroup *grp1, CfgGroup *grp2);
static void box_dlr_db_fields_destroy(box_dlr_db_fields *fields);

static void add_true(const Octstr *smsc, const Octstr *ts, Msg *msg);

#ifdef HAVE_MYSQL
static void dlr_mysql_add_with_id(box_dlr_entry *entry);
static box_dlr_entry* dlr_mysql_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_mysql(Cfg *cfg);

#ifdef HAVE_SDB
static int gw_sdb_query(char *query,int (*callback)(int, char **, void *), void *closure);
static const char* sdb_get_limit_str(void);
static int sdb_callback_find(int n, char **p, void *data);
static void dlr_sdb_add_with_id(box_dlr_entry *entry);
static box_dlr_entry* dlr_sdb_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_sdb(Cfg *cfg);

#ifdef HAVE_ORACLE
static void dlr_oracle_add_with_id(box_dlr_entry *entry);
static box_dlr_entry* dlr_oracle_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_oracle(Cfg *cfg); 

static void dlr_mem_add_with_id(box_dlr_entry *box_dlr, Msg *msg);
static int dlr_mem_entry_match(box_dlr_entry *box_dlr, const Octstr *id, int use_smpp_id);
static box_dlr_entry *dlr_mem_peek(const Octstr *id, int use_smpp_id);
static void box_dlr_mem_shutdown(void);
static box_dlr_storage *box_dlr_init_mem(Cfg *cfg);

#ifdef HAVE_PGSQL
static void dlr_pgsql_add_with_id(box_dlr_entry *entry);
static box_dlr_entry* dlr_pgsql_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_pgsql(Cfg *cfg);

#ifdef HAVE_MSSQL
static void dlr_mssql_add_with_id(box_dlr_entry *entry);
static box_dlr_entry* dlr_mssql_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_mssql(Cfg *cfg);

#ifdef HAVE_SQLITE3
static void dlr_sqlite3_add_with_id(box_dlr_entry *entry);
static box_dlr_entry *dlr_sqlite3_peek(const Octstr *id, int use_smpp_id);
#endif
static box_dlr_storage *box_dlr_init_sqlite3(Cfg *cfg);


static void box_dlr_storage_destroy(box_dlr_storage *s)
{
    gw_free(s);
}

void box_dlr_init(Cfg *cfg)
{
    CfgGroup *grp;
    Octstr *dlr_type;

    /* check which DLR storage type we are using */
    grp = cfg_get_single_group(cfg, octstr_imm("opensmppbox"));
    if(grp == NULL)
        panic(0, "opensmppbox: DLR: can't find group opensmppbox");

    dlr_type = cfg_get(grp, octstr_imm("box-dlr-storage"));

    /*
     * assume we are using internal memory in case no directive
     * has been specified, warn the user anyway
     */
    if (dlr_type == NULL) {
        dlr_type = octstr_imm("internal");
        warning(0, "opensmmpbox: DLR: using default 'internal' for storage type.");
    }
        /* call the sub-init routine */
    if (octstr_compare(dlr_type, octstr_imm("mysql")) == 0) {
        handles = box_dlr_init_mysql(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("sdb")) == 0) {
        handles = box_dlr_init_sdb(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("oracle")) == 0) {
        handles = box_dlr_init_oracle(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("internal")) == 0) {
        handles = box_dlr_init_mem(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("pgsql")) == 0) {
        handles = box_dlr_init_pgsql(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("mssql")) == 0) {
        handles = box_dlr_init_mssql(cfg);
    } else if (octstr_compare(dlr_type, octstr_imm("sqlite3")) == 0) {
        handles = box_dlr_init_sqlite3(cfg);
    }
    if (!handles) {
            panic(0, "opensmppbox: DLR: storage type '%s' is not supported!", octstr_get_cstr(dlr_type));
    }

    /* check needed function pointers */
    if (!(handles->dlr_add_with_id) || !(handles->dlr_peek))
        panic(0, "opensmppbox: DLR: storage type '%s' don't implement needed functions", octstr_get_cstr(dlr_type));

    /* get info from storage */
    info(0, "opensmppbox DLR storage using type: %s", handles->type);

    octstr_destroy(dlr_type);
}

void box_dlr_shutdown(void)
{
    dbpool_destroy(box_pool);
    box_dlr_db_fields_destroy(box_fields);
    box_dlr_storage_destroy(handles); 
}

void box_dlr_add(const Octstr *smsc, const Octstr *ts, Msg *msg)
{
    /* check if delivery receipt requested */
    if (!DLR_IS_ENABLED(msg->sms.dlr_mask))
        return;

    add_true(smsc, ts, msg);
}

void msg_add(const Octstr *smsc, const Octstr *ts, Msg *msg)
{
    add_true(smsc, ts, msg);
}

/*
 * Return Msg* if dlr entry found in DB, otherwise NULL.
 * NOTE: msg is not removed. This funsction is used to
 * fetch data from dlr table.
 */
Msg *dlr_find_by_id(const Octstr *id, int usesmpp)
{
    Msg *msg = NULL;
    box_dlr_entry *dlr = NULL;

    /* check if we have handler registered */
    if (handles == NULL || handles->dlr_peek == NULL)
        return NULL;

    debug("opensmppbox", 0, "DLR[%s]:Looking for DLR id=%s", handles->type, octstr_get_cstr(id));

    dlr = handles->dlr_peek(id, usesmpp);
    if (!dlr)  {
        warning(0, "opensmppbox DLR for ID <%s> not found.", octstr_get_cstr(id));
        return NULL;
    }

#define O_SET(x, val) if (octstr_len(val) > 0) { x = val; val = NULL; }

    msg = msg_create(sms);
    msg->sms.sms_type = report_mo;
    O_SET(msg->sms.service, dlr->entry->service);
    O_SET(msg->sms.smsc_id, dlr->entry->smsc);
    O_SET(msg->sms.receiver, dlr->entry->destination);
    O_SET(msg->sms.sender, dlr->entry->source);
    /* if dlr_url was present, recode it here again */
    O_SET(msg->sms.dlr_url, dlr->entry->url);
    /*
     * If id is available, use it to restore box id for smppbox
     * usage
     */
    O_SET(msg->sms.foreign_id, dlr->id);
    /*
     * insert original message to the data segment
     * later in the smsc module
     */
    msg->sms.msgdata = NULL;
    /*
     * If a boxc_id is available, then instruct smppbox to
     * route this msg back to originating client
     */
    O_SET(msg->sms.boxc_id, dlr->entry->boxc_id);
    time(&msg->sms.time);
    debug("opensmppbox", 0, "created DLR message for ID <%s>",
         (msg->sms.foreign_id ? octstr_get_cstr(msg->sms.foreign_id) : ""));

#undef O_SET

    /* destroy struct dlr_entry */
    box_dlr_entry_destroy(dlr);
    debug("", 0, "we have a message");
    msg_dump(msg, 0);
    return msg;
}


static void add_true(const Octstr *smsc, const Octstr *ts, Msg *msg)
{
    box_dlr_entry *dlr = NULL;

    /* Add the foreign_id so all SMSC modules can use it.
     * Obey also the original message in the split_parts list. */
    if (msg->sms.foreign_id != NULL)
        octstr_destroy(msg->sms.foreign_id);
    msg->sms.foreign_id = octstr_duplicate(ts);
    if (msg->sms.split_parts != NULL) {
        struct split_parts *split = msg->sms.split_parts;
        if (split->orig->sms.foreign_id != NULL)
            octstr_destroy(split->orig->sms.foreign_id);
        split->orig->sms.foreign_id = octstr_duplicate(ts);
    }

    /* sanity check */
    if (!handles || !msg)
        return;

    const char *type = dlr_type();
    int is_internal = 0;
    if (strcmp(type, "internal") == 0) {
        if (!handles->dlr_add_mem_with_id)
            return;
        is_internal = 1;
    } else
        if (!handles->dlr_add_with_id)
            return;          

    if (smsc && octstr_len(smsc) == 0) {
        warning(0, "opensmppbox DLR[%s]: Can't add a dlr without smsc-id", handles->type);
        return;
    }

     /* allocate new struct box_dlr_entry struct */
    dlr = box_dlr_entry_create();

    /* now copy all values, we are interested in */
    dlr->entry->smsc = (smsc ? octstr_duplicate(smsc) : octstr_create(""));
    dlr->entry->timestamp = (ts ? octstr_duplicate(ts) : octstr_create(""));
    dlr->entry->source = (msg->sms.sender ? octstr_duplicate(msg->sms.sender) : octstr_create(""));
    dlr->entry->destination = (msg->sms.receiver ? octstr_duplicate(msg->sms.receiver) : octstr_create(""));
    dlr->entry->service = (msg->sms.service ? octstr_duplicate(msg->sms.service) : octstr_create(""));
    dlr->entry->url = (msg->sms.dlr_url ? octstr_duplicate(msg->sms.dlr_url) : octstr_create(""));
    dlr->entry->boxc_id = (msg->sms.boxc_id ? octstr_duplicate(msg->sms.boxc_id) : octstr_create(""));
    dlr->entry->mask = msg->sms.dlr_mask;

    char uuidbuf[UUID_STR_LEN + 1];
    Octstr *id;
    uuid_unparse(msg->sms.id, uuidbuf);
    id = octstr_create_from_data(uuidbuf, UUID_STR_LEN + 1);
    dlr->id = octstr_duplicate(id);

    debug("opensmppbox", 0, "DLR[%s]: Adding DLR smsc=%s, ts=%s, src=%s, dst=%s, mask=%d, boxc=%s, id=%s",
          handles->type, octstr_get_cstr(dlr->entry->smsc), octstr_get_cstr(dlr->entry->timestamp),
          octstr_get_cstr(dlr->entry->source), octstr_get_cstr(dlr->entry->destination), dlr->entry->mask,
          octstr_get_cstr(dlr->entry->boxc_id), octstr_get_cstr(id));

    /* call registered function */
    if (is_internal)
        handles->dlr_add_mem_with_id(dlr, msg);
    else
        handles->dlr_add_with_id(dlr);

    octstr_destroy(id);
}

static box_dlr_entry *box_dlr_entry_create(void)
{
    box_dlr_entry *dlr;

    dlr = gw_malloc(sizeof(box_dlr_entry));
    dlr->entry = dlr_entry_create();
    dlr->id = NULL;

    return dlr;
}

static box_dlr_entry *box_dlr_entry_duplicate(const box_dlr_entry *dlr)
{
    box_dlr_entry *copy;

    if (!dlr)
        return NULL;

    copy = box_dlr_entry_create();
    copy->entry = dlr_entry_duplicate(dlr->entry);
    copy->id = octstr_duplicate(dlr->id);

    return copy;
}

static void dlr_entry_dump(const box_dlr_entry *box_dlr)
{
    if (!box_dlr) {
        debug("opensmppbox", 0, "dlr entry points to NULL");
        return;
    }

    if (box_dlr->entry->smsc)
        debug("opensmppbox", 0, "dlr entry smsc id was %s", octstr_get_cstr(box_dlr->entry->smsc));
    if (box_dlr->entry->timestamp)
        debug("opensmppbox", 0, "dlr entry timestamp was %s", octstr_get_cstr(box_dlr->entry->timestamp));
    if (box_dlr->entry->source)
        debug("opensmppbox", 0, "dlr entry source was %s", octstr_get_cstr(box_dlr->entry->source));
    if (box_dlr->entry->destination)
        debug("opensmppbox", 0, "dlr entry destination was %s", octstr_get_cstr(box_dlr->entry->destination));
    if (box_dlr->entry->service)
        debug("opensmppbox", 0, "dlr entry service  was %s", octstr_get_cstr(box_dlr->entry->service));
    if (box_dlr->entry->url)
        debug("opensmppbox", 0, "dlr entry dlr URL  was %s", octstr_get_cstr(box_dlr->entry->url));
    if (box_dlr->entry->boxc_id)
       debug("opensmppbox", 0, "dlr entry box id  was %s",  octstr_get_cstr(box_dlr->entry->boxc_id));
    if (box_dlr->id)
        debug("opensmppbox", 0, "dlr entry msg id  was %s", octstr_get_cstr(box_dlr->id));
}

void box_dlr_entry_destroy(box_dlr_entry *box_dlr)
{
    if (!box_dlr)
        return;

    dlr_entry_destroy(box_dlr->entry);
#define O_DELETE(a)      { if (a) octstr_destroy(a); a = NULL; }
    O_DELETE(box_dlr->id);
    gw_free(box_dlr);
#undef O_DELETE
}

static box_dlr_db_fields *box_dlr_db_fields_create(CfgGroup *grp1, CfgGroup *grp2)
{
    box_dlr_db_fields *fields = NULL;

    fields = gw_malloc(sizeof(box_dlr_db_fields));
    fields->dlr_db_fields = dlr_db_fields_create(grp1);
    fields->field_id = cfg_get(grp2, octstr_imm("box-msg-id"));

    return fields;
}

static void box_dlr_db_fields_destroy(box_dlr_db_fields *fields)
{
    /* sanity check */
    if (!fields)
        return;                                 

    dlr_db_fields_destroy(fields->dlr_db_fields);

#define O_DELETE(a)      { if (a) octstr_destroy(a); a = NULL; }
    O_DELETE(fields->field_id);
#undef O_DELETE

    gw_free(fields);
}

#ifdef HAVE_MYSQL

static void dlr_mysql_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql, *os_mask;
    DBPoolConn *pconn;
    List *binds = gwlist_create();
    int res;

    debug("opensmppbox", 0, "adding DLR entry wirh id into database");

    pconn = dbpool_conn_consume(box_pool);
    /* just for sure */
    if (!pconn) {
        box_dlr_entry_destroy(entry);
        return;
    }

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO `%S` (`%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`) VALUES "
                            "(?, ?, ?, ?, ?, ?, ?, ?, 0)",
                            box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc, box_fields->dlr_db_fields->field_ts,
                            box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                            box_fields->dlr_db_fields->field_status);
    else
        sql = octstr_format("INSERT INTO `%S` (`%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`) VALUES "
                            "(?, ?, ?, ?, ?, ?, ?, ?, ?, 0)",
                            box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc, box_fields->dlr_db_fields->field_ts,
                            box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_status);

    os_mask = octstr_format("%d", entry->entry->mask);
    gwlist_append(binds, entry->entry->smsc);
    gwlist_append(binds, entry->entry->timestamp);
    gwlist_append(binds, entry->entry->source);
    gwlist_append(binds, entry->entry->destination);
    gwlist_append(binds, entry->entry->service);
    gwlist_append(binds, entry->entry->url);
    gwlist_append(binds, os_mask);
    gwlist_append(binds, entry->entry->boxc_id);

    if (box_fields->field_id && octstr_len(box_fields->field_id) > 0)
        gwlist_append(binds, entry->id);
#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif
    if ((res = dbpool_conn_update(pconn, sql, binds)) == -1)
        error(0, "opensmppbox: DLR: MYSQL: Error while adding dlr entry for DST<%s>", octstr_get_cstr(entry->entry->destination));
    else if (!res)
        warning(0, "opensmppbox: DLR: MYSQL: No dlr inserted for DST<%s>", octstr_get_cstr(entry->entry->destination));

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    gwlist_destroy(binds, NULL);
    octstr_destroy(os_mask);
    box_dlr_entry_destroy(entry);
}

static box_dlr_entry* dlr_mysql_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql = NULL, *like = NULL, *smpp_id = NULL;
    DBPoolConn *pconn = NULL;
    List *result = NULL, *row = NULL;
    box_dlr_entry *res = NULL;
    List *binds = gwlist_create();

    pconn = dbpool_conn_consume(box_pool);
    if (pconn == NULL) /* should not happens, but sure is sure */
        return NULL;

    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        octstr_destroy(smpp_id);
        sql = octstr_format("SELECT `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S` FROM `%S` WHERE `%S`  %S LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like);
    } else
        sql = octstr_format("SELECT `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S`, `%S` FROM `%S` WHERE `%S`=? LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id);

    gwlist_append(binds, (Octstr *)id);

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif

    if (dbpool_conn_select(pconn, sql, binds, &result) != 0) {
        octstr_destroy(sql);
        octstr_destroy(like);
        dbpool_conn_produce(pconn);
        gwlist_destroy(result, NULL);
        return NULL;
    }
    
    octstr_destroy(sql);
    octstr_destroy(like);
    gwlist_destroy(binds, NULL);
    dbpool_conn_produce(pconn);

#define LO2CSTR(r, i) octstr_get_cstr(gwlist_get(r, i))

    if (gwlist_len(result) > 0) {
        row = gwlist_extract_first(result);
        res = box_dlr_entry_create();
        gw_assert(res != NULL);
        res->entry->mask = atoi(LO2CSTR(row,0));
        res->entry->service = octstr_create(LO2CSTR(row, 1));
        res->entry->url = octstr_create(LO2CSTR(row,2));
        res->entry->source = octstr_create(LO2CSTR(row, 3));
        res->entry->destination = octstr_create(LO2CSTR(row, 4));
        res->entry->boxc_id = octstr_create(LO2CSTR(row, 5));
        res->id = octstr_create(LO2CSTR(row, 6));
        res->entry->smsc = octstr_create(LO2CSTR(row, 7));
        gwlist_destroy(row, octstr_destroy_item);
    };

#undef LO2CSTR

    gwlist_destroy(result, NULL);
    return res;
}

static box_dlr_storage *box_dlr_init_mysql(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    Octstr *p = NULL;
    Octstr *mysql_host, *mysql_user, *mysql_pass, *mysql_db, *mysql_id;
    long mysql_port = 0;
    long pool_size;
    DBConf *db_conf = NULL;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "mysql";
    handles->dlr_add_with_id = dlr_mysql_add_with_id;
    handles->dlr_peek = dlr_mysql_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used MySQL table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: MySQL: group 'dlr-db' is not specified!");

    if (!(mysql_id = cfg_get(grp1, octstr_imm("id"))))
            panic(0, "opensmppbox: DLR: MySQL: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: MySQL: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    /*
     * Escaping special quotes for field/table names
     */
    octstr_replace(box_fields->dlr_db_fields->table, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_smsc, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_ts, octstr_imm("`"), octstr_imm("``"));
   octstr_replace(box_fields->dlr_db_fields->field_src, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_dst, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_serv, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_url, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_mask, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_status, octstr_imm("`"), octstr_imm("``"));
    octstr_replace(box_fields->dlr_db_fields->field_boxc, octstr_imm("`"), octstr_imm("``"));

    if (box_fields->field_id && octstr_len(box_fields->field_id) > 0)
        octstr_replace(box_fields->field_id, octstr_imm("`"), octstr_imm("``"));

    /*
     * now grap the required information from the 'mysql-connection' group
     * with the mysql-id we just obtained
     *
     * we have to loop through all available MySQL connection definitions
     * and search for the one we are looking for
     */

    grplist = cfg_get_multi_group(cfg, octstr_imm("mysql-connection"));
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, mysql_id) == 0) {
            goto found;
        }
        if (p != NULL) octstr_destroy(p);
    }
    panic(0, "opensmppbox: DLR: MySQL: connection settings for id '%s' are not specified!",
          octstr_get_cstr(mysql_id));
found:
    octstr_destroy(p);
    gwlist_destroy(grplist, NULL);

    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1 || pool_size == 0)
        pool_size = 1;

    if (!(mysql_host = cfg_get(grp1, octstr_imm("host"))))
            panic(0, "DLR: MySQL: directive 'host' is not specified!");
    if (!(mysql_user = cfg_get(grp1, octstr_imm("username"))))
            panic(0, "DLR: MySQL: directive 'username' is not specified!");
    if (!(mysql_pass = cfg_get(grp1, octstr_imm("password"))))
            panic(0, "DLR: MySQL: directive 'password' is not specified!");
    if (!(mysql_db = cfg_get(grp1, octstr_imm("database"))))
            panic(0, "DLR: MySQL: directive 'database' is not specified!");
    cfg_get_integer(&mysql_port, grp1, octstr_imm("port"));  /* optional */

    /*
     * ok, ready to connect to MySQL
     */
    db_conf = gw_malloc(sizeof(DBConf));
    db_conf->mysql = gw_malloc(sizeof(MySQLConf));
    db_conf->mysql->host = mysql_host;
    db_conf->mysql->port = mysql_port;
    db_conf->mysql->username = mysql_user;
    db_conf->mysql->password = mysql_pass;
    db_conf->mysql->database = mysql_db;

    box_pool = dbpool_create(DBPOOL_MYSQL, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0,"DLR: MySQL: database pool has no connections!");

    octstr_destroy(mysql_id);

    return handles;
}

#else
/*
 * Return NULL , so we point dlr-core that we were
 * not compiled in.
 */
static box_dlr_storage *box_dlr_init_mysql(Cfg *cfg)
{
    return NULL;
}

#endif

#ifdef HAVE_SDB

enum {
    SDB_ORACLE,
    SDB_MYSQL,
    SDB_POSTGRES,
    SDB_OTHER
};
 
static long sdb_conn_type = SDB_OTHER;

static int gw_sdb_query(char *query,int (*callback)(int, char **, void *), void *closure)
{
    DBPoolConn *pc;
    int rows;

    pc = dbpool_conn_consume(box_pool);
    if (pc == NULL) {
        error(0, "opensmppbox: SDB: Database pool got no connection!");
        return -1;
    }

    rows = sdb_query(pc->conn, query, callback, closure);

    dbpool_conn_produce(pc);

    return rows;
}

static const char* sdb_get_limit_str(void)
{
    switch (sdb_conn_type) {
        case SDB_ORACLE:
            return "AND ROWNUM < 2";
        case SDB_MYSQL:
        case SDB_POSTGRES:
            return "LIMIT 1";
        case SDB_OTHER:
        default:
            return "";
    }
}

static int sdb_callback_find(int n, char **p, void *data)
{
    box_dlr_entry *res = (box_dlr_entry *) data;

    if (n != 8) {
        debug("dlr.sdb", 0, "SDB: Result has incorrect number of columns: %d", n);
        return 0;
    }

#if defined(DLR_TRACE)
    debug("dlr.sdb", 0, "row=%s,%s,%s,%s,%s,%s,%s,%s",p[0],p[1],p[2],p[3],p[4],p[5],p[6],p[7]);
#endif

    res->entry->mask = atoi(p[0]);
    res->entry->service = octstr_create(p[1]);
    res->entry->url = octstr_create(p[2]);
    res->entry->source = octstr_create(p[3]);
    res->entry->destination = octstr_create(p[4]);
    res->entry->boxc_id = octstr_create(p[5]);
    res->id = octstr_create(p[6]);
    res->entry->smsc = octstr_create(p[7]);

    return 0;
}

static box_dlr_entry *dlr_sdb_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql = NULL, *smpp_id = NULL, *like = NULL;
    int state;
    box_dlr_entry *res = box_dlr_entry_create();
    
    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S %S %s",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like,
                            sdb_get_limit_str());
        octstr_destroy(smpp_id);
    } else
            sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S='%S' %s",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, id, sdb_get_limit_str());

#if defined(DLR_TRACE)
     debug("opensmppbox", 0, "SDB: sql: %s", octstr_get_cstr(sql));
#endif

    state = gw_sdb_query(octstr_get_cstr(sql), sdb_callback_find, res);
    octstr_destroy(sql);
    octstr_destroy(like);
    if (state == -1) {
        error(0, "opensmppbox: SDB: error in finding DLR");
        goto notfound;
    }
    else if (state == 0) {
        debug("opensmppbox", 0, "SDB: no entry found for ID <%s>.", octstr_get_cstr(id));
        goto notfound;
    }

    return res;

notfound:
    box_dlr_entry_destroy(res); res = NULL;
    return NULL;
}

static void dlr_sdb_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql;
    int state;
    box_dlr_entry *res = NULL;

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO %s (%s, %s, %s, %s, %s, %s, %s, %s, %s) VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d')",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), octstr_get_cstr(entry->entry->source),
                        octstr_get_cstr(entry->entry->destination), octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0);
    else
        sql = octstr_format("INSERT INTO %s (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s) VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d', '%s')",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status), octstr_get_cstr(box_fields->field_id),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), octstr_get_cstr(entry->entry->source),
                        octstr_get_cstr(entry->entry->destination), octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0, octstr_get_cstr(entry->id));

#if defined(DLR_TRACE)
    debug("dlr.sdb", 0, "SDB: sql: %s", octstr_get_cstr(sql));           
#endif

    state = gw_sdb_query(octstr_get_cstr(sql), NULL, NULL);
    if (state == -1)
        error(0, "opensmppbox: SDB: error in inserting DLR for DST <%s>", octstr_get_cstr(entry->entry->destination));

    octstr_destroy(sql);
    box_dlr_entry_destroy(entry);
}

static box_dlr_storage *box_dlr_init_sdb(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    Octstr *p = NULL;
    Octstr *sdb_url, *sdb_id;
    long pool_size;
    DBConf *db_conf = NULL;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "sdb";
    handles->dlr_add_with_id = dlr_sdb_add_with_id;
    handles->dlr_peek = dlr_sdb_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used SDB table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: SDB: group 'dlr-db' is not specified!");

    if (!(sdb_id = cfg_get(grp1, octstr_imm("id"))))
         panic(0, "opensmppbox: DLR: SDB: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: SDB: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    /*
     * now grap the required information from the 'mysql-connection' group
     * with the sdb-id we just obtained
     *
     * we have to loop through all available SDB connection definitions
     * and search for the one we are looking for
     */

    grplist = cfg_get_multi_group(cfg, octstr_imm("sdb-connection"));
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, sdb_id) == 0) {
            goto found;
        }
        if (p != NULL) octstr_destroy(p);
    }
    panic(0, "opensmppbox: DLR: SDB: connection settings for id '%s' are not specified!",
          octstr_get_cstr(sdb_id));
found:
    octstr_destroy(p);
    gwlist_destroy(grplist, NULL);

    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1 || pool_size == 0)
        pool_size = 1;

    if (!(sdb_url = cfg_get(grp1, octstr_imm("url"))))
            panic(0, "opensmppbox: DLR: SDB: directive 'url' is not specified!");

    if (octstr_search(sdb_url, octstr_imm("oracle:"), 0) == 0)
        sdb_conn_type = SDB_ORACLE;
    else if (octstr_search(sdb_url, octstr_imm("mysql:"), 0) == 0) {
        warning(0, "DLR[sdb]: Please use native MySQL support, instead of libsdb.");
        sdb_conn_type = SDB_MYSQL;
    }
    else if (octstr_search(sdb_url, octstr_imm("postgres:"), 0) == 0) {
        sdb_conn_type = SDB_POSTGRES;
    }
    else
        sdb_conn_type = SDB_OTHER;

    /*
     * ok, ready to connect
     */
    info(0,"opensmppbox connecting to sdb resource <%s>.", octstr_get_cstr(sdb_url));

    db_conf = gw_malloc(sizeof(DBConf));

    db_conf->sdb = gw_malloc(sizeof(SDBConf));
    db_conf->sdb->url = sdb_url;

    box_pool = dbpool_create(DBPOOL_SDB, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0,"opensmppbox: DLR: SDB: database pool has no connections!");

    octstr_destroy(sdb_id); sdb_id = NULL;
    return handles;
}

#else
/*
 * Return NULL , so we point dlr core that we were
 * not compiled in.
 */
static box_dlr_storage *box_dlr_init_sdb(Cfg *cfg)
{
    return NULL;
}

#endif

#ifdef HAVE_ORACLE

static void dlr_oracle_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql, *os_mask;
    DBPoolConn *pconn;
    List *binds = gwlist_create();
    int res;

    debug("opensmppbox", 0, "adding DLR entry wirh id into database");

    pconn = dbpool_conn_consume(box_pool);
    /* just for sure */
    if (!pconn) {
        box_dlr_entry_destroy(entry);
        return;
    }

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO %S (%S, %S, %S, %S, %S, %S, %S, %S, %S) VALUES "
                            "(:1, :2, :3, :4, :5, :6, :7, :8, 0)",
                            box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc, box_fields->dlr_db_fields->field_ts,
                            box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                            box_fields->dlr_db_fields->field_status);
    else
        sql = octstr_format("INSERT INTO %S (%S, %S, %S, %S, %S, %S, %S, %S, %S, %S) VALUES "
                            "(:1, :2, :3, :4, :5, :6, :7, :8, :9, 0)",
                            box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc, box_fields->dlr_db_fields->field_ts,
                            box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_status);

    os_mask = octstr_format("%d", entry->entry->mask);
    gwlist_append(binds, entry->entry->smsc);
    gwlist_append(binds, entry->entry->timestamp);
    gwlist_append(binds, entry->entry->source);
    gwlist_append(binds, entry->entry->destination);
    gwlist_append(binds, entry->entry->service);
    gwlist_append(binds, entry->entry->url);
    gwlist_append(binds, os_mask);
    gwlist_append(binds, entry->entry->boxc_id);
    if (box_fields->field_id && octstr_len(box_fields->field_id) > 0)
        gwlist_append(binds, entry->id);

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif
    if ((res = dbpool_conn_update(pconn, sql, binds)) == -1)
        error(0, "opensmppbox: DLR: ORACLE: Error while adding dlr entry for DST<%s>", octstr_get_cstr(entry->entry->destination));
    else if (!res)
        warning(0, "opensmppbox: DLR: ORACLE: No dlr inserted for DST<%s>", octstr_get_cstr(entry->entry->destination));

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    gwlist_destroy(binds, NULL);
    octstr_destroy(os_mask);
    box_dlr_entry_destroy(entry);
}

static box_dlr_entry* dlr_oracle_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql, *like, *smpp_id;
    DBPoolConn *pconn;
    List *result = NULL, *row;
    box_dlr_entry *res = NULL;
    List *binds = gwlist_create();

    pconn = dbpool_conn_consume(box_pool);
    if (pconn == NULL) /* should not happens, but sure is sure */
        return NULL;

    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S:1 %S ROWNUM < 2",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like);
        octstr_destroy(smpp_id);
    } else
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE `%S`=:1 ROWNUM < 2",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id);

    gwlist_append(binds, (Octstr *)id);

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif

    if (dbpool_conn_select(pconn, sql, binds, &result) != 0) {
        octstr_destroy(sql);
        octstr_destroy(like);
        dbpool_conn_produce(pconn);
        return NULL;
    }

    octstr_destroy(sql);
    octstr_destroy(like);
    gwlist_destroy(binds, NULL);
    dbpool_conn_produce(pconn);
#define LO2CSTR(r, i) octstr_get_cstr(gwlist_get(r, i))

    if (gwlist_len(result) > 0) {
        row = gwlist_extract_first(result);
        res = box_dlr_entry_create();
        res->entry->mask = atoi(LO2CSTR(row, 0));
        res->entry->service = octstr_create(LO2CSTR(row, 1));
        res->entry->url = octstr_create(LO2CSTR(row,2));
        res->entry->source = octstr_create(LO2CSTR(row, 3));
        res->entry->destination = octstr_create(LO2CSTR(row, 4));
        res->entry->boxc_id = octstr_create(LO2CSTR(row, 5));
        res->id = octstr_create(LO2CSTR(row, 6));
        res->entry->smsc = octstr_create(LO2CSTR(row, 7));
        gwlist_destroy(row, octstr_destroy_item);
    }
    gwlist_destroy(result, NULL);

#undef LO2CSTR

    return res;
}

static box_dlr_storage *box_dlr_init_oracle(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    Octstr *p = NULL;
    Octstr *id, *username, *password, *tnsname;
    long pool_size;
    DBConf *db_conf = NULL;
    int found;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "oracle";
    handles->dlr_add_with_id = dlr_oracle_add_with_id;
    handles->dlr_peek = dlr_oracle_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used Oracle table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: Oracle: group 'dlr-db' is not specified!");

    if (!(id = cfg_get(grp1, octstr_imm("id"))))
            panic(0, "opensmppbox: DLR: Oracle: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: Oracle: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    grplist = cfg_get_multi_group(cfg, octstr_imm("oracle-connection"));
    found = 0;
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        Octstr *p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, id) == 0) {
            found = 1;
        }
        if (p != NULL)
            octstr_destroy(p);
        if (found == 1)
            break;
    }
    gwlist_destroy(grplist, NULL);

    if (found == 0)
        panic(0, "Opensmppbox: DLR: ORACLE: connection settings for id '%s' are not specified!",
              octstr_get_cstr(id));

    username = cfg_get(grp1, octstr_imm("username"));
    password = cfg_get(grp1, octstr_imm("password"));
    tnsname = cfg_get(grp1, octstr_imm("tnsname"));
    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1)
        pool_size = 1;
                                                                        
    if (username == NULL || password == NULL || tnsname == NULL)
        panic(0, "opensmppbox: DLR: ORACLE: connection settings missing for id '%s', please"
                      " check you configuration.",octstr_get_cstr(id));

    /* ok we are ready to create dbpool */
    db_conf = gw_malloc(sizeof(*db_conf));
    db_conf->oracle = gw_malloc(sizeof(OracleConf));

    db_conf->oracle->username = username;
    db_conf->oracle->password = password;
    db_conf->oracle->tnsname = tnsname;

    box_pool = dbpool_create(DBPOOL_ORACLE, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0, "opensmppbox: DLR: ORACLE: Could not establish oracle connection(s).");

    octstr_destroy(id);

    return handles;
}

#else
/* no oracle support build in */
static box_dlr_storage *box_dlr_init_oracle(Cfg *cfg)
{
    return NULL;
}

#endif

/*
 * add box_dlr_entry to our list, and Kannel's, if storage type
 * is internal
 */
static void dlr_mem_add_with_id(box_dlr_entry *box_dlr, Msg *msg)
{
    const char *type;

    /* Remove \0 from the end of the id.*/
    octstr_delete(box_dlr->id, UUID_STR_LEN, 1);

    gw_rwlock_wrlock(&rwlock);
    gwlist_append(box_dlr_waiting_list, box_dlr);
    gw_rwlock_unlock(&rwlock);

    type = dlr_type();
    if (strcmp(type, "internal") == 0)
        dlr_add(box_dlr->entry->smsc, box_dlr->entry->timestamp, msg);
}

/*
 * Return 0 if entry match and 1 if not.
 */
static int dlr_mem_entry_match(box_dlr_entry *box_dlr, const Octstr *id, int use_smpp_id)
{
    if (use_smpp_id) {
        if (octstr_ncompare(box_dlr->id, id, 8) == 0)
            return 0;
    } else {
        if (octstr_compare(box_dlr->id, id) == 0)
            return 0;
    }

    return 1;
}

/*
 * Find matching entry and return copy of it, otherwise NULL
 */
static box_dlr_entry *dlr_mem_peek(const Octstr *id, int use_smpp_id)
{
    long i;
    long len;
    box_dlr_entry *dlr = NULL, *ret = NULL;

    gw_rwlock_rdlock(&rwlock);
    len = gwlist_len(box_dlr_waiting_list);                                 
    for (i=0; i < len; i++) {
        dlr = gwlist_get(box_dlr_waiting_list, i);

        if (dlr_mem_entry_match(dlr, id, use_smpp_id) == 0) {
            ret = box_dlr_entry_duplicate(dlr);
            break;
        }
    }
    gw_rwlock_unlock(&rwlock);

    /* we couldnt find a matching entry */
    return ret;
}

/*
 * Destroy dlr_waiting_list.
 */
static void box_dlr_mem_shutdown()
{
    gw_rwlock_wrlock(&rwlock);
    gwlist_destroy(box_dlr_waiting_list, (gwlist_item_destructor_t *)box_dlr_entry_destroy);
    gw_rwlock_unlock(&rwlock);
    gw_rwlock_destroy(&rwlock);
}

static box_dlr_storage *box_dlr_init_mem(Cfg *cfg)
{
    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "internal";
    handles->dlr_add_mem_with_id = dlr_mem_add_with_id;
    handles->dlr_peek = dlr_mem_peek;
    handles->dlr_shutdown = box_dlr_mem_shutdown;

    box_dlr_waiting_list = gwlist_create();
    gw_rwlock_init_static(&rwlock);

    return handles;
}

#ifdef HAVE_PGSQL

static void dlr_pgsql_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql;
    DBPoolConn *pconn;

    debug("opensmppbox", 0, "adding DLR entry wirh id into database");

    pconn = dbpool_conn_consume(box_pool);
    /* just for sure */
    if (!pconn) {
        box_dlr_entry_destroy(entry);
        return;
    }

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO \"%s\" (\"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\") VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d');",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), octstr_get_cstr(entry->entry->source),
                        octstr_get_cstr(entry->entry->destination), octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0);
    else
        sql = octstr_format("INSERT INTO \"%s\" (\"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\") VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d', '%s');",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status), octstr_get_cstr(box_fields->field_id),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), octstr_get_cstr(entry->entry->source),
                        octstr_get_cstr(entry->entry->destination), octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0, octstr_get_cstr(entry->id));

    if (dbpool_conn_update(pconn, sql, NULL) == -1)
        error(0, "opensmppbox: PGSQL: DB update failed!");

    dbpool_conn_produce(pconn);

    octstr_destroy(sql);
    box_dlr_entry_destroy(entry);
}

static box_dlr_entry *dlr_pgsql_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql = NULL, *like = NULL, *smpp_id = NULL;
    List *result = NULL, *row = NULL;
    box_dlr_entry *res = NULL;
    DBPoolConn *pconn;

    pconn = dbpool_conn_consume(box_pool);
    if (pconn == NULL) /* should not happens, but sure is sure */
        return NULL;

    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S %S LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like);
        octstr_destroy(smpp_id);
    } else
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S='%S' LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, id);

    if (dbpool_conn_select(pconn, sql, NULL, &result) == -1)
        error(0, "opensmppbox: PGSQL: Select failed!");

    if (result == NULL || gwlist_len(result) < 1) {
        debug("opensmppbox", 0, "PGSQL: no rows found");
        gwlist_destroy(result, NULL);
        octstr_destroy(sql);
        octstr_destroy(like);
        return NULL;
    }

    /* Note that we used id as search key; it is unique so we would have oly one
     * result row. */
    row = gwlist_get(result, 0);

    res = box_dlr_entry_create();
    res->entry->mask        = atoi(octstr_get_cstr(gwlist_get(row, 0)));
    res->entry->service     = octstr_duplicate(gwlist_get(row, 1));
    res->entry->url         = octstr_duplicate(gwlist_get(row, 2));
    res->entry->source      = octstr_duplicate(gwlist_get(row, 3));
    res->entry->destination = octstr_duplicate(gwlist_get(row, 4));
    res->entry->boxc_id     = octstr_duplicate(gwlist_get(row, 5));
    res->id                 = octstr_duplicate(gwlist_get(row, 6));
    res->entry->smsc        = octstr_duplicate(gwlist_get(row, 7));

    while((row = gwlist_extract_first(result)))
        gwlist_destroy(row, octstr_destroy_item);
    gwlist_destroy(result, NULL);
    gwlist_destroy(row, octstr_destroy_item);

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    octstr_destroy(like);
    return res;
}

static box_dlr_storage *box_dlr_init_pgsql(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    Octstr *pgsql_host, *pgsql_user, *pgsql_pass, *pgsql_db, *pgsql_id;
    long pgsql_port = 0;
    Octstr *p = NULL;
    long pool_size;
    DBConf *db_conf = NULL;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "pgsql";
    handles->dlr_add_with_id = dlr_pgsql_add_with_id;
    handles->dlr_peek = dlr_pgsql_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used Oracle table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: PgSQL: group 'dlr-db' is not specified!");

    if (!(pgsql_id = cfg_get(grp1, octstr_imm("id"))))
            panic(0, "opensmppbox: DLR: PgSQL: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: PgSQL: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    /*
     * Escaping special quotes for field/table names
     */
    octstr_replace(box_fields->dlr_db_fields->table, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_smsc, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_ts, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_src, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_dst, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_serv, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_url, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_mask, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_status, octstr_imm("\""), octstr_imm("\"\""));
    octstr_replace(box_fields->dlr_db_fields->field_boxc, octstr_imm("\""), octstr_imm("\"\""));

    if (box_fields->field_id && octstr_len(box_fields->field_id) > 0)
        octstr_replace(box_fields->field_id, octstr_imm("`"), octstr_imm("``"));

   /*
     * now grap the required information from the 'pgsql-connection' group
     * with the pgsql-id we just obtained
     *                                                                  
     * we have to loop through all available PgSQL connection definitions
     * and search for the one we are looking for
     */

    grplist = cfg_get_multi_group(cfg, octstr_imm("pgsql-connection"));
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, pgsql_id) == 0) {
            goto found;
        }
        if (p != NULL) octstr_destroy(p);
    }

    panic(0, "opensmppbox: DLR: PgSQL: connection settings for id '%s' are not specified!",
          octstr_get_cstr(pgsql_id));

found:
    octstr_destroy(p);
    gwlist_destroy(grplist, NULL);

    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1 || pool_size == 0)
        pool_size = 1;

    if (!(pgsql_host = cfg_get(grp1, octstr_imm("host"))))
            panic(0, "opensmppbox: DLR: PgSQL: directive 'host' is not specified!");
    if (!(pgsql_user = cfg_get(grp1, octstr_imm("username"))))
            panic(0, "opensmppbox: DLR: PgSQL: directive 'username' is not specified!");
    if (!(pgsql_pass = cfg_get(grp1, octstr_imm("password"))))
            panic(0, "opendmppbox: DLR: PgSQL: directive 'password' is not specified!");
    if (!(pgsql_db = cfg_get(grp1, octstr_imm("database"))))
            panic(0, "DLR: PgSQL: directive 'database' is not specified!");
    cfg_get_integer(&pgsql_port, grp1, octstr_imm("port"));  /* optional */

    /*
     * ok, ready to connect to the database
     */
    db_conf = gw_malloc(sizeof(DBConf));

    db_conf->pgsql = gw_malloc(sizeof(PgSQLConf));
    db_conf->pgsql->host = pgsql_host;
    db_conf->pgsql->port = pgsql_port;
    db_conf->pgsql->username = pgsql_user;
    db_conf->pgsql->password = pgsql_pass;
    db_conf->pgsql->database = pgsql_db;

    box_pool = dbpool_create(DBPOOL_PGSQL, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0,"DLR: PgSQL: database pool has no connections!");

    octstr_destroy(pgsql_id);

    return handles;
}

#else
/*
 * Return NULL , so we point dlr core that we were
 * not compiled in.
 */
static box_dlr_storage *box_dlr_init_pgsql(Cfg *cfg)
{
    return NULL;
}

#endif

#ifdef HAVE_MSSQL

static void dlr_mssql_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql;
    DBPoolConn *pconn;
    int res;

    debug("opensmppbox", 0, "adding DLR entry with id into database");

    pconn = dbpool_conn_consume(box_pool);
    /* just for sure */
    if (!pconn) {
        box_dlr_entry_destroy(entry);
        return;
    }

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO %s (%s, %s, %s, %s, %s, %s, %s, %s, %s) VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d')",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), 
                        octstr_get_cstr(entry->entry->source), octstr_get_cstr(entry->entry->destination), 
                        octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0);
    else
        sql = octstr_format("INSERT INTO %s (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s) VALUES "
                        "('%s', '%s', '%s', '%s', '%s', '%s', '%d', '%s', '%d', '%s')",
                        octstr_get_cstr(box_fields->dlr_db_fields->table), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_ts),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_src), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_dst),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_serv), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_url),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_mask), 
                        octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                        octstr_get_cstr(box_fields->dlr_db_fields->field_status), 
                        octstr_get_cstr(box_fields->field_id),
                        octstr_get_cstr(entry->entry->smsc), octstr_get_cstr(entry->entry->timestamp), 
                        octstr_get_cstr(entry->entry->source), octstr_get_cstr(entry->entry->destination), 
                        octstr_get_cstr(entry->entry->service), octstr_get_cstr(entry->entry->url),
                        entry->entry->mask, octstr_get_cstr(entry->entry->boxc_id), 0, 
                        octstr_get_cstr(entry->id));
#if defined(DLR_TRACE)
    debug("opensmmpbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif
    if ((res = dbpool_conn_update(pconn, sql, NULL)) == -1)
        error(0, "opensmppbox: DLR: MSSQL: Error while adding dlr entry for DST<%s>", octstr_get_cstr(entry->entry->destination));

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    box_dlr_entry_destroy(entry);
}

static box_dlr_entry *dlr_mssql_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql, *like, *smpp_id;
    List *result = NULL, *row;
    box_dlr_entry *res = NULL;
    DBPoolConn *pconn;

    pconn = dbpool_conn_consume(box_pool);
    if (pconn == NULL) /* should not happens, but sure is sure */
        return NULL;

    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        sql = octstr_format("SELECT TOP 1 %s, %s, %s, %s, %s, %s, %s, %s FROM %s WHERE %s %s",
                            octstr_get_cstr(box_fields->dlr_db_fields->field_mask), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_serv),
                            octstr_get_cstr(box_fields->dlr_db_fields->field_url), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_src),
                            octstr_get_cstr(box_fields->dlr_db_fields->field_dst), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                            octstr_get_cstr(box_fields->field_id), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                            octstr_get_cstr(box_fields->dlr_db_fields->table), 
                            octstr_get_cstr(box_fields->field_id), octstr_get_cstr(like));
        octstr_destroy(smpp_id);
        octstr_destroy(like);
    } else
         sql = octstr_format("SELECT TOP 1 %s, %s, %s, %s, %s, %s, %s, %s FROM %s WHERE %s='%s'",
                            octstr_get_cstr(box_fields->dlr_db_fields->field_mask), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_serv),
                            octstr_get_cstr(box_fields->dlr_db_fields->field_url), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_src),
                            octstr_get_cstr(box_fields->dlr_db_fields->field_dst), 
                            octstr_get_cstr(box_fields->dlr_db_fields->field_boxc),
                            octstr_get_cstr(box_fields->field_id), octstr_get_cstr(box_fields->dlr_db_fields->field_smsc),
                            octstr_get_cstr(box_fields->dlr_db_fields->table), 
                            octstr_get_cstr(box_fields->field_id), octstr_get_cstr(id));

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif
    if (dbpool_conn_select(pconn, sql, NULL, &result) != 0) {
        octstr_destroy(sql);
        dbpool_conn_produce(pconn);
        return NULL;
    }

    octstr_destroy(sql);
    dbpool_conn_produce(pconn);

    #define LO2CSTR(r, i) octstr_get_cstr(gwlist_get(r, i))             

    if (gwlist_len(result) > 0) {
        row = gwlist_extract_first(result);
        res = box_dlr_entry_create();
        res->entry->mask = atoi(LO2CSTR(row,0));
        res->entry->service = octstr_create(LO2CSTR(row, 1));
        res->entry->url = octstr_create(LO2CSTR(row,2));
        res->entry->source = octstr_create(LO2CSTR(row, 3));
        res->entry->destination = octstr_create(LO2CSTR(row, 4));
        res->entry->boxc_id = octstr_create(LO2CSTR(row, 5));
        res->id = octstr_create(LO2CSTR(row, 6));
        res->entry->smsc = octstr_create(LO2CSTR(row, 7));
        gwlist_destroy(row, octstr_destroy_item);
    }
    gwlist_destroy(result, NULL);

#undef LO2CSTR

    return res;
}

static box_dlr_storage *box_dlr_init_mssql(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    long pool_size;
    DBConf *db_conf = NULL;
    Octstr *id, *username, *password, *server, *database;
    int found;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "mssql";
    handles->dlr_add_with_id = dlr_mssql_add_with_id;
    handles->dlr_peek = dlr_mssql_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used MSSQL table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: MSSQL: group 'dlr-db' is not specified!");

    if (!(id = cfg_get(grp1, octstr_imm("id"))))
        panic(0, "opensmppbox: DLR: MSSQL: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: MSSQL: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    grplist = cfg_get_multi_group(cfg, octstr_imm("mssql-connection"));
    found = 0;
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        Octstr *p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, id) == 0) {
            found = 1;
        }
        if (p != NULL)
            octstr_destroy(p);
        if (found == 1)
            break;
    }
    gwlist_destroy(grplist, NULL);

  if (found == 0)                                                     
        panic(0, "opensmppbox: DLR: MSSQL: connection settings for id '%s' are not specified!",
              octstr_get_cstr(id));

    username = cfg_get(grp1, octstr_imm("username"));
    password = cfg_get(grp1, octstr_imm("password"));
    server = cfg_get(grp1, octstr_imm("server"));
    database = cfg_get(grp1, octstr_imm("database"));
    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1)
        pool_size = 1;

    if (username == NULL || password == NULL || server == NULL || database == NULL) {
        panic(0, "opensmppbox: DLR: MSSQL: connection settings missing for id '%s'. "
              "Please check you configuration.", octstr_get_cstr(id));
    }

    /* ok we are ready to create dbpool */
    db_conf = gw_malloc(sizeof(*db_conf));
    db_conf->mssql = gw_malloc(sizeof(MSSQLConf));

    db_conf->mssql->username = username;
    db_conf->mssql->password = password;
    db_conf->mssql->server = server;
    db_conf->mssql->database = database;

    box_pool = dbpool_create(DBPOOL_MSSQL, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0, "opensmppbox: DLR: MSSQL: Could not establish mssql connection(s).");

    octstr_destroy(id);
    octstr_destroy(database);

    return handles;
}

#else
/* no mssql support build in */
static box_dlr_storage *box_dlr_init_mssql(Cfg *cfg)
{
    return NULL;
}

#endif

#ifdef HAVE_SQLITE3

static void dlr_sqlite3_add_with_id(box_dlr_entry *entry)
{
    Octstr *sql, *os_mask;
    DBPoolConn *pconn;
    List *binds = gwlist_create();
    int res;

    debug("opensmppbox", 0, "adding DLR entry into database");

    pconn = dbpool_conn_consume(box_pool);
    /* just for sure */
    if (pconn == NULL) {
        box_dlr_entry_destroy(entry);
        return;
    }

    if (box_fields->field_id == NULL || octstr_len(box_fields->field_id) == 0)
        sql = octstr_format("INSERT INTO %S (%S, %S, %S, %S, %S, %S, %S, %S, %S) VALUES "
                        "(?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, 0)",
                        box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc,
                        box_fields->dlr_db_fields->field_ts,
                        box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst,
                        box_fields->dlr_db_fields->field_serv, box_fields->dlr_db_fields->field_url,
                        box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                        box_fields->dlr_db_fields->field_status);
    else
        sql = octstr_format("INSERT INTO %S (%S, %S, %S, %S, %S, %S, %S, %S, %S, %S) VALUES "
                        "(?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, 0, ?9)",
                        box_fields->dlr_db_fields->table, box_fields->dlr_db_fields->field_smsc,
                        box_fields->dlr_db_fields->field_ts,
                        box_fields->dlr_db_fields->field_src, box_fields->dlr_db_fields->field_dst,
                        box_fields->dlr_db_fields->field_serv, box_fields->dlr_db_fields->field_url,
                        box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_boxc,
                        box_fields->dlr_db_fields->field_status, box_fields->field_id);
1
#if defined(DLR_TRACE)
    debug("opensmmpbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif

    os_mask = octstr_format("%d", entry->entry->mask);

    gwlist_append(binds, entry->entry->smsc);         /* ?1 */
    gwlist_append(binds, entry->entry->timestamp);    /* ?2 */
    gwlist_append(binds, entry->entry->source);       /* ?3 */
    gwlist_append(binds, entry->entry->destination);  /* ?4 */
    gwlist_append(binds, entry->entry->service);      /* ?5 */
    gwlist_append(binds, entry->entry->url);          /* ?6 */
    gwlist_append(binds, os_mask);                    /* ?7 */
    gwlist_append(binds, entry->entry->boxc_id);      /* ?8 */

    if (box_fields->field_id && octstr_len(box_fields->field_id) > 0)
        gwlist_append(binds, entry->id);              /* ?9 */

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif                                                                  
    if ((res = dbpool_conn_update(pconn, sql, binds)) == -1)
        error(0, "DLR: SQLite3: Error while adding dlr entry for DST<%s>", octstr_get_cstr(entry->entry->destination));
    else if (!res)
        warning(0, "DLR: SQLite3: No dlr inserted for DST<%s>", octstr_get_cstr(entry->entry->destination));

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    gwlist_destroy(binds, NULL);
    octstr_destroy(os_mask);
    box_dlr_entry_destroy(entry);
}

static box_dlr_entry *dlr_sqlite3_peek(const Octstr *id, int use_smpp_id)
{
    Octstr *sql = NULL, *like = NULL, *smpp_id = NULL;
    DBPoolConn *pconn = NULL;
    List *result = NULL, *row = NULL;
    box_dlr_entry *res = NULL;
    List *binds = gwlist_create();

    pconn = dbpool_conn_consume(box_pool);
    if (pconn == NULL) /* should not happens, but sure is sure */
        return NULL;

    if (use_smpp_id) {
        smpp_id = octstr_copy(id, 0, 8);
        like = octstr_format("LIKE '%s%%'", octstr_get_cstr(smpp_id));
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S %S LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like);
        octstr_destroy(smpp_id);
    } else {
        like = octstr_format("LIKE '%s'", octstr_get_cstr(id));
        sql = octstr_format("SELECT %S, %S, %S, %S, %S, %S, %S, %S FROM %S WHERE %S %S LIMIT 1",
                            box_fields->dlr_db_fields->field_mask, box_fields->dlr_db_fields->field_serv,
                            box_fields->dlr_db_fields->field_url, box_fields->dlr_db_fields->field_src,
                            box_fields->dlr_db_fields->field_dst, box_fields->dlr_db_fields->field_boxc,
                            box_fields->field_id, box_fields->dlr_db_fields->field_smsc,
                            box_fields->dlr_db_fields->table, box_fields->field_id, like);
   }

#if defined(DLR_TRACE)
    debug("opensmppbox", 0, "sql: %s", octstr_get_cstr(sql));
#endif
    if (dbpool_conn_select(pconn, sql, binds, &result) != 0) {
        octstr_destroy(sql);
        dbpool_conn_produce(pconn);
        return NULL;
    }

    dbpool_conn_produce(pconn);
    octstr_destroy(sql);
    octstr_destroy(like);
    gwlist_destroy(binds, NULL);

#define LO2CSTR(r, i) octstr_get_cstr(gwlist_get(r, i))
    /* We have only one roe - we asked only for one. */
    if (gwlist_len(result) > 0) {
        row = gwlist_extract_first(result);
        res = box_dlr_entry_create();
        res->entry->mask = atoi(LO2CSTR(row,0));
        res->entry->service = octstr_create(LO2CSTR(row, 1));
        res->entry->url = octstr_create(LO2CSTR(row,2));
        res->entry->source = octstr_create(LO2CSTR(row, 3));
        res->entry->destination = octstr_create(LO2CSTR(row, 4));
        res->entry->boxc_id = octstr_create(LO2CSTR(row, 5));
        res->id = octstr_create(LO2CSTR(row,6));
        res->entry->smsc = octstr_create(LO2CSTR(row,7));
        gwlist_destroy(row, octstr_destroy_item);
    }
    gwlist_destroy(result, NULL);

#undef LO2CSTR

    return res;
}

static box_dlr_storage *box_dlr_init_sqlite3(Cfg *cfg)
{
    CfgGroup *grp1, *grp2;
    List *grplist;
    long pool_size;
    DBConf *db_conf = NULL;
    Octstr *id, *file;
    int found;

    handles = gw_malloc(sizeof(box_dlr_storage));
    handles->type = "sqlite3";
    handles->dlr_add_with_id = dlr_sqlite3_add_with_id;
    handles->dlr_peek = dlr_sqlite3_peek;
    handles->dlr_shutdown = box_dlr_shutdown;

    /*
     * check for all mandatory directives that specify the field names
     * of the used SQLite table
     */
    if (!(grp1 = cfg_get_single_group(cfg, octstr_imm("dlr-db"))))
        panic(0, "opensmppbox: DLR: SQLite3: group 'dlr-db' is not specified!");

    if (!(id = cfg_get(grp1, octstr_imm("id"))))
            panic(0, "opensmppbox: DLR: SQLite3: directive 'id' is not specified!");

    if (!(grp2 = cfg_get_single_group(cfg, octstr_imm("opensmppbox"))))
        panic(0, "opensmppbox: DLR: SQLite3: group 'opensmppbox' is not specified!");

    box_fields = box_dlr_db_fields_create(grp1, grp2);

    grplist = cfg_get_multi_group(cfg, octstr_imm("sqlite3-connection"));
    found = 0;
    while (grplist && (grp1 = gwlist_extract_first(grplist)) != NULL) {
        Octstr *p = cfg_get(grp1, octstr_imm("id"));
        if (p != NULL && octstr_compare(p, id) == 0) {
            found = 1;
        }
        if (p != NULL)
            octstr_destroy(p);
        if (found == 1)
            break;
    }
    gwlist_destroy(grplist, NULL);

    if (found == 0)
        panic(0, "opensmppbox: DLR: SQLite3: connection settings for id '%s' are not specified!",
              octstr_get_cstr(id));

    file = cfg_get(grp1, octstr_imm("database"));
    if (cfg_get_integer(&pool_size, grp1, octstr_imm("max-connections")) == -1)
        pool_size = 1;

    if (file == NULL)
        panic(0, "opensmppbox: DLR: SQLite3: connection settings missing for id '%s', please"
                 " check you configuration.",octstr_get_cstr(id));

    /* ok we are ready to create dbpool */
    db_conf = gw_malloc(sizeof(*db_conf));
    db_conf->sqlite3 = gw_malloc(sizeof(SQLite3Conf));

    db_conf->sqlite3->file = file;

    box_pool = dbpool_create(DBPOOL_SQLITE3, db_conf, pool_size);

    if (dbpool_conn_count(box_pool) == 0)
        panic(0, "DLR: SQLite3: Could not establish sqlite3 connection(s).");

    octstr_destroy(id);

    return handles;
}

#else
/* no sqlite3 support build in */
static box_dlr_storage *box_dlr_init_sqlite3(Cfg *cfg)
{
    return NULL;
}

#endif
