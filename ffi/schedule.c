/*
 * schedule.h's structs to the Lean model's values and back.
 *
 * The Lean side (proof/Timeshare/Export.lean) is the model's interface as
 * C functions, lean_ts_*: constructors from numbers and strings, decide
 * and roundRobin themselves, and a projection for each field of an answer.
 * So nothing here knows how Lean lays out a structure. What it does have to
 * get right is whose each object is, by Lean's rule for exported
 * functions: an argument is consumed, a result is ours. An element read out
 * of an array (lean_array_get_core) is borrowed, so it is lean_inc'd before
 * each projection of it.
 *
 * This file is glue, and no theorem is about it; the Go tests compare
 * every answer that comes through it with the Go code's.
 */
#include "schedule.h"

#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

/* Lean's runtime */
extern void lean_initialize_runtime_module(void);
extern void lean_internal_set_thread_stack_size(size_t);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Timeshare_Export(uint8_t builtin);

/* proof/Timeshare/Export.lean */
extern lean_object *lean_ts_opt(uint8_t has, lean_object *s);
extern lean_object *lean_ts_card(lean_object *id, uint8_t st, lean_object *model, lean_object *owner, lean_object *next,
                                 uint64_t inflight, uint64_t turn_at, uint64_t busy_at, uint64_t load);
extern lean_object *lean_ts_flow(lean_object *tenant, lean_object *model, uint64_t queued, uint64_t oldest);
extern lean_object *lean_ts_slots(lean_object *model, uint64_t n);
extern lean_object *lean_ts_line(lean_object *tenant, lean_object *models);
extern lean_object *lean_ts_policy(uint64_t max_timeslice, uint64_t load_ratio, uint64_t idle);
extern lean_object *lean_ts_decide(lean_object *cards, lean_object *flows, lean_object *slots, lean_object *lines,
                                   uint64_t now, lean_object *policy);
extern lean_object *lean_ts_decision_actions(lean_object *decision);
extern lean_object *lean_ts_decision_lines(lean_object *decision);
extern uint8_t lean_ts_action_kind(lean_object *action);
extern lean_object *lean_ts_action_card(lean_object *action);
extern lean_object *lean_ts_action_model(lean_object *action);
extern lean_object *lean_ts_action_tenant(lean_object *action);
extern lean_object *lean_ts_action_next(lean_object *action);
extern lean_object *lean_ts_line_tenant(lean_object *line);
extern lean_object *lean_ts_line_models(lean_object *line);
extern uint8_t lean_ts_opt_is_some(lean_object *opt);
extern lean_object *lean_ts_opt_get(lean_object *opt);
extern lean_object *lean_ts_queue(lean_object *tenant, uint64_t inflight, lean_object *keys);
extern lean_object *lean_ts_owner(lean_object *tenant, uint64_t held, uint64_t slots);
extern lean_object *lean_ts_round_robin(lean_object *queues, lean_object *owner, lean_object *after, uint64_t n);
extern lean_object *lean_ts_picks_requests(lean_object *picks);
extern lean_object *lean_ts_picks_last(lean_object *picks);
extern uint64_t lean_ts_req_queue(lean_object *req);
extern uint64_t lean_ts_req_index(lean_object *req);

int ts_init(void) {
	/* Lean gives the thread it starts here a stack of 1 GB unless told
	 * otherwise; none of the scheduler runs on it. A machine with less
	 * memory than that refuses ("failed to create thread") and the program
	 * dies. */
	lean_internal_set_thread_stack_size((size_t)8 << 20);
	lean_initialize_runtime_module();
	lean_object *r = initialize_Timeshare_Export(1);
	int ok = lean_io_result_is_ok(r);
	lean_dec_ref(r);
	if (!ok) return -1;
	lean_io_mark_end_initialization();
	return 0;
}

/* ---- C to Lean: each returns an object that is the caller's -------------- */

static lean_object *str(const char *s) { return lean_mk_string(s ? s : ""); }

static lean_object *opt(const char *s) { return lean_ts_opt(s != NULL, str(s)); }

static lean_object *strs(const char *const *ss, size_t n) {
	lean_object *a = lean_mk_empty_array();
	for (size_t i = 0; i < n; i++) a = lean_array_push(a, str(ss[i]));
	return a;
}

/* ---- Lean to C ------------------------------------------------------------
 * Everything an answer points to is carved from one block (struct first,
 * then the arrays, then the strings), so one free releases it. `need`
 * counts the bytes, `fill` hands them out. */

typedef struct {
	char *at;
} block;

static void *take(block *b, size_t n) {
	/* keep what follows aligned for a pointer or a uint64_t */
	n = (n + 7) & ~(size_t)7;
	void *p = b->at;
	b->at += n;
	return p;
}

static size_t padded(size_t n) { return (n + 7) & ~(size_t)7; }

/* The text of a Lean string we own, copied into the block; the string is
 * released. */
static const char *take_str(block *b, lean_object *s) {
	size_t n = strlen(lean_string_cstr(s)) + 1;
	char *p = take(b, n);
	memcpy(p, lean_string_cstr(s), n);
	lean_dec(s);
	return p;
}

/* The same for an Option String we own (it is released too): NULL for none. */
static const char *take_opt(block *b, lean_object *o) {
	lean_inc(o);
	if (!lean_ts_opt_is_some(o)) {
		lean_dec(o);
		return NULL;
	}
	return take_str(b, lean_ts_opt_get(o));
}

static size_t str_size(lean_object *s) {
	size_t n = padded(strlen(lean_string_cstr(s)) + 1);
	lean_dec(s);
	return n;
}

static size_t opt_size(lean_object *o) {
	lean_inc(o);
	if (!lean_ts_opt_is_some(o)) {
		lean_dec(o);
		return 0;
	}
	return str_size(lean_ts_opt_get(o));
}

/* a reference of our own to something borrowed */
static lean_object *dup(lean_object *x) {
	lean_inc(x);
	return x;
}

/* x is borrowed; f consumes its argument */
#define GET(f, x) f(dup(x))

const ts_decision *ts_decide(const ts_round *r) {
	for (size_t i = 0; i < r->n_cards; i++)
		if ((unsigned)r->cards[i].state > TS_DRAINING) return NULL;

	lean_object *cards = lean_mk_empty_array();
	for (size_t i = 0; i < r->n_cards; i++) {
		const ts_card *c = &r->cards[i];
		cards = lean_array_push(cards, lean_ts_card(str(c->id), (uint8_t)c->state, opt(c->model), opt(c->owner),
		                                            opt(c->next), c->inflight, c->turn_at, c->busy_at, c->load));
	}
	lean_object *flows = lean_mk_empty_array();
	for (size_t i = 0; i < r->n_flows; i++) {
		const ts_flow *f = &r->flows[i];
		flows = lean_array_push(flows, lean_ts_flow(str(f->tenant), str(f->model), f->queued, f->oldest));
	}
	lean_object *slots = lean_mk_empty_array();
	for (size_t i = 0; i < r->n_slots; i++)
		slots = lean_array_push(slots, lean_ts_slots(str(r->slots[i].model), r->slots[i].slots));
	lean_object *lines = lean_mk_empty_array();
	for (size_t i = 0; i < r->n_lines; i++) {
		const ts_line *l = &r->lines[i];
		lines = lean_array_push(lines, lean_ts_line(str(l->tenant), strs(l->models, l->n_models)));
	}
	lean_object *pol = lean_ts_policy(r->policy.max_timeslice, r->policy.load_ratio, r->policy.idle);

	lean_object *d = lean_ts_decide(cards, flows, slots, lines, r->now, pol);
	lean_object *acts = GET(lean_ts_decision_actions, d);
	lean_object *out = lean_ts_decision_lines(d); /* the last use of d */
	size_t n_acts = lean_array_size(acts), n_out = lean_array_size(out);

	size_t need = padded(sizeof(ts_decision)) + padded(n_acts * sizeof(ts_action)) + padded(n_out * sizeof(ts_line));
	for (size_t i = 0; i < n_acts; i++) {
		lean_object *a = lean_array_get_core(acts, i);
		need += str_size(GET(lean_ts_action_card, a)) + opt_size(GET(lean_ts_action_model, a)) +
		        opt_size(GET(lean_ts_action_tenant, a)) + opt_size(GET(lean_ts_action_next, a));
	}
	for (size_t i = 0; i < n_out; i++) {
		lean_object *l = lean_array_get_core(out, i);
		lean_object *ms = GET(lean_ts_line_models, l);
		need += str_size(GET(lean_ts_line_tenant, l)) + padded(lean_array_size(ms) * sizeof(char *));
		for (size_t j = 0; j < lean_array_size(ms); j++) need += str_size(dup(lean_array_get_core(ms, j)));
		lean_dec(ms);
	}

	block b = {malloc(need)};
	if (!b.at) {
		lean_dec(acts);
		lean_dec(out);
		return NULL;
	}
	ts_decision *res = take(&b, sizeof(ts_decision));
	ts_action *as = take(&b, n_acts * sizeof(ts_action));
	ts_line *ls = take(&b, n_out * sizeof(ts_line));
	res->actions = as;
	res->n_actions = n_acts;
	res->lines = ls;
	res->n_lines = n_out;
	for (size_t i = 0; i < n_acts; i++) {
		lean_object *a = lean_array_get_core(acts, i);
		as[i].kind = (ts_kind)GET(lean_ts_action_kind, a);
		as[i].card = take_str(&b, GET(lean_ts_action_card, a));
		as[i].model = take_opt(&b, GET(lean_ts_action_model, a));
		as[i].tenant = take_opt(&b, GET(lean_ts_action_tenant, a));
		as[i].next = take_opt(&b, GET(lean_ts_action_next, a));
	}
	for (size_t i = 0; i < n_out; i++) {
		lean_object *l = lean_array_get_core(out, i);
		lean_object *ms = GET(lean_ts_line_models, l);
		size_t n = lean_array_size(ms);
		ls[i].tenant = take_str(&b, GET(lean_ts_line_tenant, l));
		const char **models = take(&b, n * sizeof(char *));
		for (size_t j = 0; j < n; j++) models[j] = take_str(&b, dup(lean_array_get_core(ms, j)));
		ls[i].models = models;
		ls[i].n_models = n;
		lean_dec(ms);
	}
	lean_dec(acts);
	lean_dec(out);
	return res;
}

void ts_decision_free(const ts_decision *d) { free((void *)d); }

const ts_picks *ts_round_robin(const ts_queue *queues, size_t n_queues, ts_owner own, const char *after, uint64_t n) {
	lean_object *qs = lean_mk_empty_array();
	for (size_t i = 0; i < n_queues; i++) {
		const ts_queue *q = &queues[i];
		qs = lean_array_push(qs, lean_ts_queue(str(q->tenant), q->inflight, strs(q->keys, q->n_keys)));
	}
	lean_object *p = lean_ts_round_robin(qs, lean_ts_owner(opt(own.tenant), own.held, own.slots), opt(after), n);
	lean_object *reqs = GET(lean_ts_picks_requests, p);
	lean_object *last = lean_ts_picks_last(p); /* the last use of p */
	size_t n_picks = lean_array_size(reqs);

	block b = {malloc(padded(sizeof(ts_picks)) + padded(n_picks * sizeof(ts_pick)) + opt_size(dup(last)))};
	if (!b.at) {
		lean_dec(reqs);
		lean_dec(last);
		return NULL;
	}
	ts_picks *res = take(&b, sizeof(ts_picks));
	ts_pick *picks = take(&b, n_picks * sizeof(ts_pick));
	for (size_t i = 0; i < n_picks; i++) {
		lean_object *r = lean_array_get_core(reqs, i);
		picks[i].queue = (size_t)GET(lean_ts_req_queue, r);
		picks[i].request = (size_t)GET(lean_ts_req_index, r);
	}
	res->picks = picks;
	res->n_picks = n_picks;
	res->last = take_opt(&b, last);
	lean_dec(reqs);
	return res;
}

void ts_picks_free(const ts_picks *p) { free((void *)p); }
