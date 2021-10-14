/*
 * Copyright (c) 2016--2021  Wu, Xingbo <wuxb45@gmail.com>
 *
 * All rights reserved. No warranty, explicit or implicit, provided.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

struct litemap;
struct literef;

// litemap {{{
// the wh created by litemap_create() can work with all of safe/unsafe operations.
  extern struct litemap *
litemap_create(const struct kvmap_mm * const mm);

  extern struct kv *
litemap_get(struct literef * const ref, const struct kref * const key, struct kv * const out);

  extern bool
litemap_put(struct literef * const ref, struct kv * const kv);

  extern bool
litemap_del(struct literef * const ref, const struct kref * const key);

  extern struct litemap_iter *
litemap_iter_create(struct literef * const ref);

  extern void
litemap_iter_seek(struct litemap_iter * const iter, const struct kref * const key);

  extern bool
litemap_iter_valid(struct litemap_iter * const iter);

  extern struct kv *
litemap_iter_peek(struct litemap_iter * const iter, struct kv * const out);

  extern bool
litemap_iter_kref(struct litemap_iter * const iter, struct kref * const kref);

  extern bool
litemap_iter_kvref(struct litemap_iter * const iter, struct kvref * const kvref);

  extern void
litemap_iter_skip1(struct litemap_iter * const iter);

  extern void
litemap_iter_skip(struct litemap_iter * const iter, const u32 nr);

  extern struct kv *
litemap_iter_next(struct litemap_iter * const iter, struct kv * const out);

  extern bool
litemap_iter_inp(struct litemap_iter * const iter, kv_inp_func uf, void * const priv);

  extern void
litemap_iter_park(struct litemap_iter * const iter);

  extern void
litemap_iter_destroy(struct litemap_iter * const iter);

  extern struct literef *
litemap_ref(struct litemap * const map);

  extern struct litemap *
litemap_unref(struct literef * const ref);

  extern void
litemap_park(struct literef * const ref);

  extern void
litemap_resume(struct literef * const ref);

  extern void
litemap_refresh_qstate(struct literef * const ref);

// clean with more threads
  extern void
litemap_clean_th(struct litemap * const map, const u32 nr_threads);

  extern void
litemap_clean(struct litemap * const map);

  extern void
litemap_destroy(struct litemap * const map);

// safe API (no need to refresh qstate)

  extern struct kv *
whsafe_get(struct literef * const ref, const struct kref * const key, struct kv * const out);

  extern bool
whsafe_put(struct literef * const ref, struct kv * const kv);

  extern bool
whsafe_del(struct literef * const ref, const struct kref * const key);

// use litemap_iter_create
  extern void
whsafe_iter_seek(struct litemap_iter * const iter, const struct kref * const key);

  extern struct kv *
whsafe_iter_peek(struct litemap_iter * const iter, struct kv * const out);

// use litemap_iter_valid
// use litemap_iter_peek
// use litemap_iter_kref
// use litemap_iter_kvref
// use litemap_iter_skip1
// use litemap_iter_skip
// use litemap_iter_next
// use litemap_iter_inp

  extern void
whsafe_iter_park(struct litemap_iter * const iter);

  extern void
whsafe_iter_destroy(struct litemap_iter * const iter);

  extern struct literef *
whsafe_ref(struct litemap * const map);

// }}} litemap

#ifdef __cplusplus
}
#endif
// vim:fdm=marker
