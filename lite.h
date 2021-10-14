/*
 * Copyright (c) 2016--2021  Wu, Xingbo <wuxb45@gmail.com>
 *
 * All rights reserved. No warranty, explicit or implicit, provided.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

struct litehole;
struct literef;

// litehole {{{
// the wh created by litehole_create() can work with all of safe/unsafe operations.
  extern struct litehole *
litehole_create(const struct kvmap_mm * const mm);

  extern struct kv *
litehole_get(struct literef * const ref, const struct kref * const key, struct kv * const out);

  extern bool
litehole_put(struct literef * const ref, struct kv * const kv);

  extern bool
litehole_del(struct literef * const ref, const struct kref * const key);

  extern struct litehole_iter *
litehole_iter_create(struct literef * const ref);

  extern void
litehole_iter_seek(struct litehole_iter * const iter, const struct kref * const key);

  extern bool
litehole_iter_valid(struct litehole_iter * const iter);

  extern struct kv *
litehole_iter_peek(struct litehole_iter * const iter, struct kv * const out);

  extern bool
litehole_iter_kref(struct litehole_iter * const iter, struct kref * const kref);

  extern bool
litehole_iter_kvref(struct litehole_iter * const iter, struct kvref * const kvref);

  extern void
litehole_iter_skip1(struct litehole_iter * const iter);

  extern void
litehole_iter_skip(struct litehole_iter * const iter, const u32 nr);

  extern struct kv *
litehole_iter_next(struct litehole_iter * const iter, struct kv * const out);

  extern bool
litehole_iter_inp(struct litehole_iter * const iter, kv_inp_func uf, void * const priv);

  extern void
litehole_iter_park(struct litehole_iter * const iter);

  extern void
litehole_iter_destroy(struct litehole_iter * const iter);

  extern struct literef *
litehole_ref(struct litehole * const map);

  extern struct litehole *
litehole_unref(struct literef * const ref);

  extern void
litehole_park(struct literef * const ref);

  extern void
litehole_resume(struct literef * const ref);

  extern void
litehole_refresh_qstate(struct literef * const ref);

// clean with more threads
  extern void
litehole_clean_th(struct litehole * const map, const u32 nr_threads);

  extern void
litehole_clean(struct litehole * const map);

  extern void
litehole_destroy(struct litehole * const map);

// safe API (no need to refresh qstate)

  extern struct kv *
whsafe_get(struct literef * const ref, const struct kref * const key, struct kv * const out);

  extern bool
whsafe_put(struct literef * const ref, struct kv * const kv);

  extern bool
whsafe_del(struct literef * const ref, const struct kref * const key);

// use litehole_iter_create
  extern void
whsafe_iter_seek(struct litehole_iter * const iter, const struct kref * const key);

  extern struct kv *
whsafe_iter_peek(struct litehole_iter * const iter, struct kv * const out);

// use litehole_iter_valid
// use litehole_iter_peek
// use litehole_iter_kref
// use litehole_iter_kvref
// use litehole_iter_skip1
// use litehole_iter_skip
// use litehole_iter_next
// use litehole_iter_inp

  extern void
whsafe_iter_park(struct litehole_iter * const iter);

  extern void
whsafe_iter_destroy(struct litehole_iter * const iter);

  extern struct literef *
whsafe_ref(struct litehole * const map);

// }}} litehole

#ifdef __cplusplus
}
#endif
// vim:fdm=marker
