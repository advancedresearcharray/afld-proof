/*
 * Bridge-Guided Discovery Priority Scorer
 *
 * Scores pending discoveries by their potential to create bridges
 * to currently-unconnected domains. Writes priority scores into
 * discovery_engine_intelligence so the proof runner can pick
 * high-value items first.
 *
 * Strategy:
 *   1. Load the set of domains already connected via gap theories
 *   2. Load the set of ALL domains with proven discoveries
 *   3. Unconnected = AllDomains - Connected
 *   4. For pending items, score higher if their domain is unconnected
 *      or if their title references an unconnected domain
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mysql.h>

#define DB_HOST "192.168.167.221"
#define DB_USER "ck"
#define DB_PASS "notyou"
#define DB_NAME "math_engine"
#define MAX_DOMAINS 200
#define DOMAIN_MAX  128

static char connected[MAX_DOMAINS][DOMAIN_MAX];
static int  connected_cnt = 0;

static char all_domains[MAX_DOMAINS][DOMAIN_MAX];
static int  all_cnt = 0;

static char unconnected[MAX_DOMAINS][DOMAIN_MAX];
static int  unconnected_cnt = 0;

static int is_in_list(const char *name, char list[][DOMAIN_MAX], int cnt) {
    for (int i = 0; i < cnt; i++)
        if (strcmp(list[i], name) == 0) return 1;
    return 0;
}

static int load_connected(MYSQL *conn) {
    const char *q =
        "SELECT DISTINCT "
        "  CASE "
        "    WHEN title LIKE 'Gap theory between %% and %%' THEN "
        "      SUBSTRING_INDEX(SUBSTRING_INDEX(title, 'Gap theory between ', -1), ' and ', 1) "
        "  END as d "
        "FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' AND title LIKE 'Gap theory between%%' "
        "HAVING d IS NOT NULL AND d != '' "
        "UNION "
        "SELECT DISTINCT "
        "  TRIM(SUBSTRING_INDEX(SUBSTRING_INDEX( "
        "    SUBSTRING_INDEX(title, 'Gap theory between ', -1), ' and ', -1), ':', 1)) "
        "FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' AND title LIKE 'Gap theory between%%'";

    if (mysql_query(conn, q)) { fprintf(stderr, "%s\n", mysql_error(conn)); return -1; }
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return -1;

    MYSQL_ROW row;
    while ((row = mysql_fetch_row(res)) && connected_cnt < MAX_DOMAINS) {
        if (row[0] && strlen(row[0]) > 0 && strlen(row[0]) < DOMAIN_MAX) {
            strncpy(connected[connected_cnt], row[0], DOMAIN_MAX - 1);
            connected_cnt++;
        }
    }
    mysql_free_result(res);
    return 0;
}

static int load_all_domains(MYSQL *conn) {
    const char *q =
        "SELECT DISTINCT domain FROM array_1000y_breakthroughs "
        "WHERE proof_status='proven' ORDER BY domain";

    if (mysql_query(conn, q)) { fprintf(stderr, "%s\n", mysql_error(conn)); return -1; }
    MYSQL_RES *res = mysql_store_result(conn);
    if (!res) return -1;

    MYSQL_ROW row;
    while ((row = mysql_fetch_row(res)) && all_cnt < MAX_DOMAINS) {
        if (row[0] && strlen(row[0]) > 0 && strlen(row[0]) < DOMAIN_MAX) {
            strncpy(all_domains[all_cnt], row[0], DOMAIN_MAX - 1);
            all_cnt++;
        }
    }
    mysql_free_result(res);
    return 0;
}

static void compute_unconnected(void) {
    for (int i = 0; i < all_cnt; i++) {
        if (!is_in_list(all_domains[i], connected, connected_cnt)) {
            strncpy(unconnected[unconnected_cnt], all_domains[i], DOMAIN_MAX - 1);
            unconnected_cnt++;
        }
    }
}

static void store_priority_data(MYSQL *conn) {
    char data[8192];
    int pos = 0;

    pos += snprintf(data + pos, sizeof(data) - pos,
        "{\"connected_domains\": %d, \"all_domains\": %d, \"unconnected_domains\": %d, ",
        connected_cnt, all_cnt, unconnected_cnt);

    pos += snprintf(data + pos, sizeof(data) - pos, "\"unconnected_list\": [");
    for (int i = 0; i < unconnected_cnt && i < 50; i++) {
        if (i > 0) pos += snprintf(data + pos, sizeof(data) - pos, ", ");
        pos += snprintf(data + pos, sizeof(data) - pos, "\"%s\"", unconnected[i]);
    }
    pos += snprintf(data + pos, sizeof(data) - pos, "], ");

    pos += snprintf(data + pos, sizeof(data) - pos, "\"priority_domains\": [");
    int first = 1;
    for (int i = 0; i < unconnected_cnt; i++) {
        char q[512];
        snprintf(q, sizeof(q),
            "SELECT COUNT(*) FROM array_1000y_breakthroughs "
            "WHERE proof_status='pending' AND domain='%s'", unconnected[i]);
        if (mysql_query(conn, q)) continue;
        MYSQL_RES *res = mysql_store_result(conn);
        if (!res) continue;
        MYSQL_ROW row = mysql_fetch_row(res);
        int pending = row ? atoi(row[0]) : 0;
        mysql_free_result(res);

        if (pending > 0) {
            if (!first) pos += snprintf(data + pos, sizeof(data) - pos, ", ");
            pos += snprintf(data + pos, sizeof(data) - pos,
                "{\"domain\": \"%s\", \"pending\": %d}", unconnected[i], pending);
            first = 0;
        }
    }
    pos += snprintf(data + pos, sizeof(data) - pos, "]}");

    char esc[16384];
    mysql_real_escape_string(conn, esc, data, strlen(data));

    char q[20000];
    snprintf(q, sizeof(q),
        "INSERT INTO discovery_engine_intelligence "
        "(engine_name, insight_type, insight_data, updated_at) "
        "VALUES ('bridge_priority_scorer', 'unconnected_domains', '%s', NOW()) "
        "ON DUPLICATE KEY UPDATE insight_data=VALUES(insight_data), updated_at=NOW()", esc);
    if (mysql_query(conn, q))
        fprintf(stderr, "store: %s\n", mysql_error(conn));
}

int main(void) {
    printf("=== Bridge-Guided Discovery Priority Scorer ===\n");

    MYSQL *conn = mysql_init(NULL);
    if (!conn) return 1;
    if (!mysql_real_connect(conn, DB_HOST, DB_USER, DB_PASS, DB_NAME, 0, NULL, 0)) {
        fprintf(stderr, "%s\n", mysql_error(conn));
        return 1;
    }
    mysql_set_character_set(conn, "utf8mb4");

    load_connected(conn);
    printf("Connected domains: %d\n", connected_cnt);

    load_all_domains(conn);
    printf("All proven domains: %d\n", all_cnt);

    compute_unconnected();
    printf("Unconnected domains: %d\n\n", unconnected_cnt);

    printf("=== Unconnected Domains (need gap theory bridges) ===\n");
    for (int i = 0; i < unconnected_cnt; i++)
        printf("  %s\n", unconnected[i]);

    store_priority_data(conn);
    printf("\nPriority data stored in discovery_engine_intelligence.\n");

    mysql_close(conn);
    return 0;
}
