/*
 * Bridge Type Classifier
 *
 * Scans all proven gap theories and cross-domain bridges, classifies
 * them by mathematical construct type, and writes the classification
 * into the discovery_engine_intelligence table.
 *
 * Also computes the full domain adjacency matrix and bridge statistics.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mysql.h>

#define DB_HOST "192.168.167.221"
#define DB_USER "ck"
#define DB_PASS "notyou"
#define DB_NAME "math_engine"

#define MAX_ITEMS   5000
#define MAX_DOMAINS 100
#define TITLE_MAX   1024
#define DOMAIN_MAX  128
#define TYPE_MAX    64

typedef struct {
    int  id;
    char domain_a[DOMAIN_MAX];
    char domain_b[DOMAIN_MAX];
    char bridge_type[TYPE_MAX];
    double impact;
} ClassifiedBridge;

static ClassifiedBridge items[MAX_ITEMS];
static int item_count = 0;

static char domain_names[MAX_DOMAINS][DOMAIN_MAX];
static int  domain_cnt = 0;
static int  adj[MAX_DOMAINS][MAX_DOMAINS];

static char type_names[32][TYPE_MAX];
static int  type_counts[32];
static int  type_cnt = 0;

static int find_or_add_domain(const char *name) {
    for (int i = 0; i < domain_cnt; i++)
        if (strcmp(domain_names[i], name) == 0) return i;
    if (domain_cnt < MAX_DOMAINS) {
        strncpy(domain_names[domain_cnt], name, DOMAIN_MAX - 1);
        return domain_cnt++;
    }
    return -1;
}

static int find_or_add_type(const char *t) {
    for (int i = 0; i < type_cnt; i++)
        if (strcmp(type_names[i], t) == 0) { type_counts[i]++; return i; }
    if (type_cnt < 32) {
        strncpy(type_names[type_cnt], t, TYPE_MAX - 1);
        type_counts[type_cnt] = 1;
        return type_cnt++;
    }
    return -1;
}

static void classify(const char *title, char *out, size_t sz) {
    if (strstr(title, "Shannon Entropy") || strstr(title, "H(X) =") ||
        strstr(title, "H(p)=") || strstr(title, "C_BSC"))
        snprintf(out, sz, "shannon_entropy");
    else if (strstr(title, "Cache Hit Rate") || strstr(title, "Periodic Cache"))
        snprintf(out, sz, "cache_hit_rate");
    else if (strstr(title, "Database") && strstr(title, "Folding"))
        snprintf(out, sz, "database_folding");
    else if (strstr(title, "Network Throughput") && strstr(title, "Folding"))
        snprintf(out, sz, "network_throughput_folding");
    else if (strstr(title, "φ(") || strstr(title, "Euler Totient"))
        snprintf(out, sz, "euler_totient");
    else if (strstr(title, "Characteristic polynomial") || strstr(title, "eigenvalue"))
        snprintf(out, sz, "matrix_eigenvalue");
    else if (strstr(title, "SAT") && strstr(title, "Flow"))
        snprintf(out, sz, "sat_information_flow");
    else if (strstr(title, "Sorting") && strstr(title, "Bound"))
        snprintf(out, sz, "sorting_bound");
    else if (strstr(title, "T(n)") && strstr(title, "T(n/"))
        snprintf(out, sz, "master_theorem");
    else if (strstr(title, "Composition Preservation"))
        snprintf(out, sz, "composition_preservation");
    else if (strstr(title, "r^k") || strstr(title, "geometric") || strstr(title, "Geometric"))
        snprintf(out, sz, "geometric_series");
    else if (strstr(title, "Quadrant Scaling"))
        snprintf(out, sz, "quadrant_scaling");
    else if (strstr(title, "Transitive chain"))
        snprintf(out, sz, "transitive_chain");
    else if (strstr(title, "fp:") || strstr(title, "D1="))
        snprintf(out, sz, "dimensional_fingerprint");
    else if (strstr(title, "BCS") || strstr(title, "superconducti"))
        snprintf(out, sz, "bcs_superconductivity");
    else if (strstr(title, "Basel") || strstr(title, "ζ(2)"))
        snprintf(out, sz, "basel_zeta");
    else
        snprintf(out, sz, "general");
}

static int parse_domains(const char *title, char *da, char *db) {
    const char *p = strstr(title, "Gap theory between ");
    if (!p) return -1;
    p += strlen("Gap theory between ");

    const char *sep = strstr(p, " and ");
    if (!sep) return -1;

    size_t la = sep - p;
    if (la >= DOMAIN_MAX) la = DOMAIN_MAX - 1;
    strncpy(da, p, la); da[la] = '\0';

    const char *bs = sep + 5;
    const char *be = strchr(bs, ':');
    if (!be) be = bs + strlen(bs);
    size_t lb = be - bs;
    if (lb >= DOMAIN_MAX) lb = DOMAIN_MAX - 1;
    strncpy(db, bs, lb); db[lb] = '\0';
    while (lb > 0 && db[lb - 1] == ' ') db[--lb] = '\0';
    return 0;
}

static int load_and_classify(MYSQL *conn) {
    const char *q =
        "SELECT id, REPLACE(REPLACE(title,'\\n',' '),'\\r','') as t, impact "
        "FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' AND title LIKE 'Gap theory between%' "
        "ORDER BY impact DESC LIMIT 5000";

    if (mysql_query(conn, q)) { fprintf(stderr, "%s\n", mysql_error(conn)); return -1; }
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return -1;

    MYSQL_ROW row;
    while ((row = mysql_fetch_row(res)) && item_count < MAX_ITEMS) {
        ClassifiedBridge *b = &items[item_count];
        b->id = atoi(row[0]);
        b->impact = atof(row[2]);

        if (parse_domains(row[1], b->domain_a, b->domain_b) < 0) continue;
        classify(row[1], b->bridge_type, TYPE_MAX);
        find_or_add_type(b->bridge_type);

        int ia = find_or_add_domain(b->domain_a);
        int ib = find_or_add_domain(b->domain_b);
        if (ia >= 0 && ib >= 0) {
            adj[ia][ib]++;
            adj[ib][ia]++;
        }
        item_count++;
    }
    mysql_free_result(res);
    return 0;
}

static void print_graph_stats(void) {
    printf("\n=== Domain Adjacency Graph ===\n");
    printf("Nodes (domains): %d\n", domain_cnt);

    int edges = 0;
    for (int i = 0; i < domain_cnt; i++)
        for (int j = i + 1; j < domain_cnt; j++)
            if (adj[i][j] > 0) edges++;
    printf("Edges (connected pairs): %d\n", edges);
    printf("Max possible edges: %d\n", domain_cnt * (domain_cnt - 1) / 2);
    printf("Density: %.2f%%\n", edges * 100.0 / (domain_cnt * (domain_cnt - 1) / 2.0));

    printf("\n=== Hub Nodes (by degree) ===\n");
    for (int i = 0; i < domain_cnt; i++) {
        int degree = 0, total_bridges = 0;
        for (int j = 0; j < domain_cnt; j++) {
            if (adj[i][j] > 0) { degree++; total_bridges += adj[i][j]; }
        }
        if (degree >= 5)
            printf("  %-35s degree=%2d  bridges=%d\n", domain_names[i], degree, total_bridges);
    }

    printf("\n=== Bridge Type Distribution ===\n");
    for (int i = 0; i < type_cnt; i++)
        printf("  %-30s %d\n", type_names[i], type_counts[i]);
}

static void store_graph(MYSQL *conn) {
    char data[8192];
    int pos = 0;
    pos += snprintf(data + pos, sizeof(data) - pos,
        "{\"domains\": %d, \"edges\": ", domain_cnt);

    int edges = 0;
    for (int i = 0; i < domain_cnt; i++)
        for (int j = i + 1; j < domain_cnt; j++)
            if (adj[i][j] > 0) edges++;

    pos += snprintf(data + pos, sizeof(data) - pos, "%d, ", edges);
    pos += snprintf(data + pos, sizeof(data) - pos, "\"bridge_types\": {");
    for (int i = 0; i < type_cnt; i++) {
        if (i > 0) pos += snprintf(data + pos, sizeof(data) - pos, ", ");
        pos += snprintf(data + pos, sizeof(data) - pos, "\"%s\": %d", type_names[i], type_counts[i]);
    }
    pos += snprintf(data + pos, sizeof(data) - pos, "}, \"total_bridges\": %d}", item_count);

    char esc[16384];
    mysql_real_escape_string(conn, esc, data, strlen(data));

    char q[20000];
    snprintf(q, sizeof(q),
        "INSERT INTO discovery_engine_intelligence "
        "(engine_name, insight_type, insight_data, updated_at) "
        "VALUES ('bridge_classifier', 'domain_graph', '%s', NOW()) "
        "ON DUPLICATE KEY UPDATE insight_data=VALUES(insight_data), updated_at=NOW()", esc);
    mysql_query(conn, q);

    char hub_data[4096];
    pos = 0;
    pos += snprintf(hub_data + pos, sizeof(hub_data) - pos, "{\"hubs\": [");
    int first = 1;
    for (int i = 0; i < domain_cnt; i++) {
        int degree = 0;
        for (int j = 0; j < domain_cnt; j++)
            if (adj[i][j] > 0) degree++;
        if (degree >= 5) {
            if (!first) pos += snprintf(hub_data + pos, sizeof(hub_data) - pos, ", ");
            pos += snprintf(hub_data + pos, sizeof(hub_data) - pos,
                "{\"domain\": \"%s\", \"degree\": %d}", domain_names[i], degree);
            first = 0;
        }
    }
    pos += snprintf(hub_data + pos, sizeof(hub_data) - pos, "]}");

    mysql_real_escape_string(conn, esc, hub_data, strlen(hub_data));
    snprintf(q, sizeof(q),
        "INSERT INTO discovery_engine_intelligence "
        "(engine_name, insight_type, insight_data, updated_at) "
        "VALUES ('bridge_classifier', 'hub_nodes', '%s', NOW()) "
        "ON DUPLICATE KEY UPDATE insight_data=VALUES(insight_data), updated_at=NOW()", esc);
    mysql_query(conn, q);
}

int main(void) {
    printf("=== Bridge Type Classifier & Domain Graph Builder ===\n");

    MYSQL *conn = mysql_init(NULL);
    if (!conn) return 1;
    if (!mysql_real_connect(conn, DB_HOST, DB_USER, DB_PASS, DB_NAME, 0, NULL, 0)) {
        fprintf(stderr, "%s\n", mysql_error(conn));
        return 1;
    }
    mysql_set_character_set(conn, "utf8mb4");

    if (load_and_classify(conn) < 0) { mysql_close(conn); return 1; }

    printf("\nClassified %d gap theories\n", item_count);
    print_graph_stats();
    store_graph(conn);
    printf("\nGraph data stored in discovery_engine_intelligence.\n");

    mysql_close(conn);
    return 0;
}
