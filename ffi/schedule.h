/*
 * libschedule: the scheduler, for C.
 *
 * The algorithm is the Lean model of proof/Timeshare/Policy.lean, compiled
 * by Lean, and the theorems of proof/Timeshare/Proofs are about it. This
 * is the plain C face of it: structs in, structs out, no Lean types.
 * schedule.c turns one into the other and is not proved.
 *
 * Strings are NUL-terminated UTF-8. Where a field says "or NULL", NULL is
 * "none"; every other string must be there (it may be empty). Numbers are
 * in whatever one unit of time the caller keeps (the Go program:
 * nanoseconds). The caller owns what it passes in; nothing is kept. What
 * comes back is one allocation's worth, released with its _free.
 *
 * ts_init once, first. Then every call from the thread that called
 * ts_init: Lean's runtime keeps state by thread.
 */
#ifndef SCHEDULE_H
#define SCHEDULE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Start Lean's runtime and the model. 0, or -1 if the model would not
 * initialize. */
int ts_init(void);

/* ---- which model on which card: Decide ---------------------------------- */

typedef enum { TS_DOWN = 0, TS_STARTING = 1, TS_UP = 2, TS_DRAINING = 3 } ts_state;

/* One GPU. */
typedef struct {
	const char *id;
	ts_state state;
	const char *model;  /* what is on it, or NULL */
	const char *owner;  /* the tenant whose turn it is, or NULL */
	const char *next;   /* the model it drains for or has drained for, or NULL */
	uint64_t inflight;  /* requests being answered on it */
	uint64_t turn_at;   /* when this turn began */
	uint64_t busy_at;   /* the last time it had work */
	uint64_t load;      /* how long the model took to load */
} ts_card;

/* One tenant's queued requests for one model (not the ones in flight). */
typedef struct {
	const char *tenant;
	const char *model;
	uint64_t queued;
	uint64_t oldest;    /* its oldest queued request: newcomers join the lines in this order */
} ts_flow;

/* How many requests a model answers at once on one card. */
typedef struct {
	const char *model;
	uint64_t slots;
} ts_slots;

/* A tenant with queued requests, and its models with queued requests: the
 * first has waited longest. An array of these, in order, is "the lines". */
typedef struct {
	const char *tenant;
	const char *const *models;
	size_t n_models;
} ts_line;

typedef struct {
	uint64_t max_timeslice; /* a turn can't be taken before it is this old */
	uint64_t load_ratio;    /* nor before it is this many times the model's load time */
	uint64_t idle;          /* an idle card stops after this long (0: never) */
} ts_policy;

/* Everything a round sees. */
typedef struct {
	const ts_card *cards;
	size_t n_cards;
	const ts_flow *flows;
	size_t n_flows;
	const ts_slots *slots;  /* a model not named here has none */
	size_t n_slots;
	const ts_line *lines;   /* as the last round left them */
	size_t n_lines;
	uint64_t now;
	ts_policy policy;
} ts_round;

typedef enum { TS_START = 0, TS_STOP = 1, TS_DRAIN = 2, TS_PASS = 3 } ts_kind;

typedef struct {
	ts_kind kind;
	const char *card;
	const char *model;  /* START: what to load. Or NULL */
	const char *tenant; /* START, DRAIN, PASS: whose turn it is, or will be. Or NULL */
	const char *next;   /* DRAIN: the model the card drains for. Or NULL */
} ts_action;

typedef struct {
	const ts_action *actions; /* to apply in order */
	size_t n_actions;
	const ts_line *lines;     /* the lines afterwards: hand them to the next round */
	size_t n_lines;
} ts_decision;

/* One round: what to do with the cards now. NULL if the round can't be
 * read (a state that is none of ts_state) or memory ran out. */
const ts_decision *ts_decide(const ts_round *round);
void ts_decision_free(const ts_decision *decision);

/* ---- which requests a model that is up gets: RoundRobin ------------------ */

/* One tenant's queued requests for the model. */
typedef struct {
	const char *tenant;
	uint64_t inflight;        /* its requests being answered now */
	const char *const *keys;  /* each queued request's key, oldest first: no two picks share one */
	size_t n_keys;
} ts_queue;

/* The tenant whose turn it is on the card, and how many of the card's
 * slots its requests hold now. */
typedef struct {
	const char *tenant; /* or NULL */
	uint64_t held;
	uint64_t slots;
} ts_owner;

/* A request picked: queues[queue].keys[request]. */
typedef struct {
	size_t queue;
	size_t request;
} ts_pick;

typedef struct {
	const ts_pick *picks; /* in order */
	size_t n_picks;
	const char *last;     /* the tenant served last (the next call's `after`), or NULL if nothing was picked */
} ts_picks;

/* Up to n of the queued requests, for a model's free slots. The queues
 * must be in the order of their tenants' names (strcmp). after: the tenant
 * served last by the call before, or NULL. NULL if memory ran out. */
const ts_picks *ts_round_robin(const ts_queue *queues, size_t n_queues, ts_owner owner, const char *after, uint64_t n);
void ts_picks_free(const ts_picks *picks);

#ifdef __cplusplus
}
#endif

#endif
