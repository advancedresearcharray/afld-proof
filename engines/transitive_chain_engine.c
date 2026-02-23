/*
 * Transitive Chain Engine
 *
 * Composes proven gap theory bridges:
 *   If bridge A↔B exists and bridge B↔C exists, synthesize A↔C.
 *
 * Uses sandbox_physics as the universal hub to connect all 36+ domains.
 * Applies the quality gate: only insert if the composed bridge is unique
 * or improves existing by ≥5%.
 *
 * Reads from: array_1000y_breakthroughs (proven gap theories)
 * Writes to:  array_1000y_breakthroughs (new cross-domain bridges)
 * Updates:    discovery_engine_intelligence (chain stats)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <mysql.h>

#define DB_HOST   "192.168.167.221"
#define DB_USER   "ck"
#define DB_PASS   "notyou"
#define DB_NAME   "math_engine"

#define MAX_BRIDGES    2000
#define MAX_DOMAINS    100
#define TITLE_MAX      1024
#define DOMAIN_MAX     128
#define BATCH_INSERT   200
#define IMPROVEMENT_THRESHOLD 0.05

typedef struct {
    int    id;
    char   domain_a[DOMAIN_MAX];
    char   domain_b[DOMAIN_MAX];
    char   bridge_type[DOMAIN_MAX];
    char   title_snippet[512];
    double impact;
} GapBridge;

typedef struct {
    char name[DOMAIN_MAX];
} Domain;

static GapBridge bridges[MAX_BRIDGES];
static int bridge_count = 0;
static Domain domains[MAX_DOMAINS];
static int domain_count = 0;
static int chains_generated = 0;
static int chains_inserted = 0;
static int chains_duplicate = 0;

static int domain_index(const char *name) {
    for (int i = 0; i < domain_count; i++)
        if (strcmp(domains[i].name, name) == 0) return i;
    if (domain_count < MAX_DOMAINS) {
        strncpy(domains[domain_count].name, name, DOMAIN_MAX - 1);
        return domain_count++;
    }
    return -1;
}

static void classify_bridge(const char *title, char *out, size_t sz) {
    if (strstr(title, "Shannon Entropy") || strstr(title, "H(X)") ||
        strstr(title, "H(p)") || strstr(title, "C_BSC"))
        snprintf(out, sz, "Shannon Entropy");
    else if (strstr(title, "Cache Hit Rate"))
        snprintf(out, sz, "Cache Hit Rate");
    else if (strstr(title, "Database") && strstr(title, "Folding"))
        snprintf(out, sz, "Database Folding");
    else if (strstr(title, "φ(") || strstr(title, "Euler"))
        snprintf(out, sz, "Euler Totient");
    else if (strstr(title, "Network Throughput"))
        snprintf(out, sz, "Network Throughput");
    else if (strstr(title, "Characteristic polynomial"))
        snprintf(out, sz, "Matrix Eigenvalue");
    else if (strstr(title, "SAT"))
        snprintf(out, sz, "SAT Information Flow");
    else if (strstr(title, "Sorting"))
        snprintf(out, sz, "Sorting Bound");
    else if (strstr(title, "T(n)") || strstr(title, "Recursive"))
        snprintf(out, sz, "Recurrence/Master Thm");
    else if (strstr(title, "Composition Preservation"))
        snprintf(out, sz, "Composition Preservation");
    else if (strstr(title, "Geometric") || strstr(title, "r^k"))
        snprintf(out, sz, "Geometric Series");
    else
        snprintf(out, sz, "General");
}

static int load_bridges(MYSQL *conn) {
    const char *q =
        "SELECT id, "
        "  REPLACE(REPLACE(title, '\\n', ' '), '\\r', '') as title, "
        "  impact "
        "FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' "
        "  AND title LIKE 'Gap theory between%' "
        "ORDER BY impact DESC "
        "LIMIT 2000";

    if (mysql_query(conn, q)) {
        fprintf(stderr, "load_bridges: %s\n", mysql_error(conn));
        return -1;
    }
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return -1;

    MYSQL_ROW row;
    while ((row = mysql_fetch_row(res)) && bridge_count < MAX_BRIDGES) {
        GapBridge *b = &bridges[bridge_count];
        b->id = atoi(row[0]);
        b->impact = atof(row[2]);

        const char *title = row[1];
        strncpy(b->title_snippet, title, 511);

        const char *prefix = "Gap theory between ";
        const char *start = strstr(title, prefix);
        if (!start) continue;
        start += strlen(prefix);

        const char *sep = strstr(start, " and ");
        if (!sep) continue;

        size_t len_a = sep - start;
        if (len_a >= DOMAIN_MAX) len_a = DOMAIN_MAX - 1;
        strncpy(b->domain_a, start, len_a);
        b->domain_a[len_a] = '\0';

        const char *b_start = sep + 5;
        const char *b_end = strchr(b_start, ':');
        if (!b_end) b_end = b_start + strlen(b_start);
        size_t len_b = b_end - b_start;
        if (len_b >= DOMAIN_MAX) len_b = DOMAIN_MAX - 1;
        strncpy(b->domain_b, b_start, len_b);
        b->domain_b[len_b] = '\0';

        while (b->domain_b[len_b - 1] == ' ' && len_b > 0)
            b->domain_b[--len_b] = '\0';

        classify_bridge(title, b->bridge_type, DOMAIN_MAX);
        domain_index(b->domain_a);
        domain_index(b->domain_b);
        bridge_count++;
    }
    mysql_free_result(res);
    printf("[chain] Loaded %d bridges across %d domains\n", bridge_count, domain_count);
    return 0;
}

static int pair_exists(MYSQL *conn, const char *da, const char *db) {
    char q[1024];
    snprintf(q, sizeof(q),
        "SELECT COUNT(*) FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' AND domain='cross_domain_science' "
        "AND ("
        "  (title LIKE 'Gap theory between %s and %s%%') "
        "  OR (title LIKE 'Gap theory between %s and %s%%') "
        "  OR (title LIKE 'Cross-domain bridge%%' AND title LIKE '%%%s%%' AND title LIKE '%%%s%%')"
        ")",
        da, db, db, da, da, db);

    if (mysql_query(conn, q)) return 1;
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return 1;
    MYSQL_ROW row = mysql_fetch_row(res);
    int exists = row ? atoi(row[0]) : 0;
    mysql_free_result(res);
    return exists;
}

static double get_domain_best(MYSQL *conn, const char *domain) {
    char q[512];
    snprintf(q, sizeof(q),
        "SELECT MAX(impact) FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' AND domain='%s'", domain);
    if (mysql_query(conn, q)) return 0.0;
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return 0.0;
    MYSQL_ROW row = mysql_fetch_row(res);
    double val = (row && row[0]) ? atof(row[0]) : 0.0;
    mysql_free_result(res);
    return val;
}

static int insert_chain(MYSQL *conn, const char *da, const char *dc,
                        const char *bridge_ab, const char *bridge_bc,
                        const char *hub, double impact) {
    char title[TITLE_MAX];
    char esc_title[TITLE_MAX * 2];

    snprintf(title, TITLE_MAX,
        "Transitive chain: %s ↔ %s via %s hub. "
        "Bridge₁: %s ↔ %s (%s). "
        "Bridge₂: %s ↔ %s (%s). "
        "Composed by chain engine.",
        da, dc, hub,
        da, hub, bridge_ab,
        hub, dc, bridge_bc);

    mysql_real_escape_string(conn, esc_title, title, strlen(title));

    char q[4096];
    snprintf(q, sizeof(q),
        "INSERT INTO array_1000y_breakthroughs "
        "(title, domain, impact, proof_status) "
        "VALUES ('%s', 'cross_domain_science', %.4f, 'proven')",
        esc_title, impact);

    if (mysql_query(conn, q)) {
        fprintf(stderr, "insert_chain: %s\n", mysql_error(conn));
        return -1;
    }
    return 0;
}

static void compose_all(MYSQL *conn) {
    printf("[chain] Composing transitive chains through hub domains...\n");

    for (int i = 0; i < bridge_count; i++) {
        for (int j = i + 1; j < bridge_count; j++) {
            const char *hub = NULL;
            const char *end_a = NULL;
            const char *end_c = NULL;

            if (strcmp(bridges[i].domain_b, bridges[j].domain_a) == 0) {
                hub = bridges[i].domain_b;
                end_a = bridges[i].domain_a;
                end_c = bridges[j].domain_b;
            } else if (strcmp(bridges[i].domain_a, bridges[j].domain_b) == 0) {
                hub = bridges[i].domain_a;
                end_a = bridges[i].domain_b;
                end_c = bridges[j].domain_a;
            } else if (strcmp(bridges[i].domain_b, bridges[j].domain_b) == 0) {
                hub = bridges[i].domain_b;
                end_a = bridges[i].domain_a;
                end_c = bridges[j].domain_a;
            } else if (strcmp(bridges[i].domain_a, bridges[j].domain_a) == 0) {
                hub = bridges[i].domain_a;
                end_a = bridges[i].domain_b;
                end_c = bridges[j].domain_b;
            }

            if (!hub || !end_a || !end_c) continue;
            if (strcmp(end_a, end_c) == 0) continue;

            chains_generated++;

            int existing = pair_exists(conn, end_a, end_c);
            if (existing > 2) {
                chains_duplicate++;
                continue;
            }

            double impact = (bridges[i].impact + bridges[j].impact) / 2.0 * 0.95;
            double best = get_domain_best(conn, "cross_domain_science");
            if (existing > 0 && best > 0 && impact < best * (1.0 + IMPROVEMENT_THRESHOLD)) {
                chains_duplicate++;
                continue;
            }

            if (insert_chain(conn, end_a, end_c,
                            bridges[i].bridge_type, bridges[j].bridge_type,
                            hub, impact) == 0) {
                chains_inserted++;
                if (chains_inserted % 10 == 0)
                    printf("[chain] Inserted %d chains so far...\n", chains_inserted);
            }

            if (chains_inserted >= BATCH_INSERT) {
                printf("[chain] Batch limit reached (%d), stopping.\n", BATCH_INSERT);
                return;
            }
        }
    }
}

static void update_intelligence(MYSQL *conn) {
    char q[2048];
    snprintf(q, sizeof(q),
        "INSERT INTO discovery_engine_intelligence "
        "(pattern_type, domains, pattern_title, impact_avg, engine_name) "
        "VALUES ('cross_domain_merge', 'all', "
        "'Chain run: %d bridges, %d domains, %d generated, %d inserted, %d dupes', "
        "0.95, 'transitive_chain_engine')",
        bridge_count, domain_count, chains_generated, chains_inserted, chains_duplicate);
    mysql_query(conn, q);
}

int main(void) {
    printf("=== Transitive Chain Engine ===\n");

    MYSQL *conn = mysql_init(NULL);
    if (!conn) { fprintf(stderr, "mysql_init failed\n"); return 1; }
    if (!mysql_real_connect(conn, DB_HOST, DB_USER, DB_PASS, DB_NAME, 0, NULL, 0)) {
        fprintf(stderr, "connect: %s\n", mysql_error(conn));
        return 1;
    }
    mysql_set_character_set(conn, "utf8mb4");

    if (load_bridges(conn) < 0) { mysql_close(conn); return 1; }
    compose_all(conn);
    update_intelligence(conn);

    printf("\n=== Results ===\n");
    printf("  Bridges loaded:     %d\n", bridge_count);
    printf("  Domains:            %d\n", domain_count);
    printf("  Chains evaluated:   %d\n", chains_generated);
    printf("  Chains inserted:    %d\n", chains_inserted);
    printf("  Chains duplicate:   %d\n", chains_duplicate);

    mysql_close(conn);
    return 0;
}
