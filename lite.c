/*
 * Copyright (c) 2016--2021  Wu, Xingbo <wuxb45@gmail.com>
 *
 * All rights reserved. No warranty, explicit or implicit, provided.
 */
#define _GNU_SOURCE

// headers {{{
#include <assert.h> // static_assert
#include "lib.h"
#include "ctypes.h"
#include "kv.h"
#include "lite.h"
// }}} headers

// def {{{
#define WH_SLABLEAF_SIZE ((1lu << 21)) // 2MB for valgrind

#define WH_KPN ((128u)) // keys per node; power of 2
#define WH_KPN_MASK ((WH_KPN - 1))
#define WH_MID ((WH_KPN >> 1)) // ideal cut point for split, the closer the better

#define WH_KPN_MRG (((WH_KPN + WH_MID) >> 1 )) // 3/4
// }}} def

// struct {{{
struct liteleaf {
  // first line
  rwlock leaflock;
  u32 padding;
  au64 lv; // version (dont use the first u64)
  struct liteleaf * prev; // prev leaf
  struct liteleaf * next; // next leaf
  struct kv * anchor;

  u32 nr_keys;
  u32 reserved[5];

  struct kv * kvs[WH_KPN];
};

struct litehmap {
  au64 hv;
  u64 padding[7];

  u64 nkeys;
  u64 nalloc;

  struct {
    struct liteleaf * leaf;
    struct kv * anchor;
  } * pairs;
  u64 padding1[5];
};

struct litehole {
  // 1 line
  union {
    volatile au64 hmap_ptr; // safe
    struct litehmap * hmap; // unsafe
  };
  u64 padding0[6];
  struct liteleaf * leaf0; // usually not used
  // 1 line
  struct kvmap_mm mm;
  struct qsbr * qsbr;
  struct slab * slab_leaf;
  u32 padding1[4];
  // 2 lines
  struct litehmap hmap2[2];
  // fifth line
  rwlock metalock;
  u32 padding2[15];
};

struct litehole_iter {
  struct literef * ref; // safe-iter only
  struct litehole * map;
  struct liteleaf * leaf;
  u32 is;
};

struct literef {
  struct litehole * map;
  struct qsbr_ref qref;
};
// }}} struct

// helpers {{{

// alloc {{{
  static struct liteleaf *
liteleaf_alloc(struct litehole * const map, struct liteleaf * const prev,
    struct liteleaf * const next, struct kv * const anchor)
{
  struct liteleaf * const leaf = slab_alloc_safe(map->slab_leaf);
  if (leaf == NULL)
    return NULL;

  rwlock_init(&(leaf->leaflock));

  // keep the old version; new version will be assigned by split functions
  //leaf->lv = 0;

  leaf->prev = prev;
  leaf->next = next;
  leaf->anchor = anchor;

  leaf->nr_keys = 0;
  return leaf;
}

  static void
liteleaf_free(struct slab * const slab, struct liteleaf * const leaf)
{
  debug_assert(leaf->leaflock.opaque == 0);
  free(leaf->anchor);
  slab_free_safe(slab, leaf);
}

  static inline bool
litehole_hmap_reserve(struct litehole * const map, const u32 nr)
{
#ifdef ALLOCFAIL
  if (alloc_fail())
    return false;
#endif
  for (u32 i = 0; i < 2; i++) {
    struct litehmap * const hmap = &map->hmap2[i];
    if (hmap->nkeys + nr > hmap->nalloc) { // try realloc
      const u64 n1 = hmap->nalloc + 256;
      void * const pairs1 = realloc(hmap->pairs, sizeof(hmap->pairs[0]) * n1);
      if (pairs1 == NULL)
        return false;
      hmap->nalloc = n1;
      hmap->pairs = pairs1;
    }
  }
  return true;
}
// }}} alloc

// lock {{{
  static void
liteleaf_lock_write(struct liteleaf * const leaf, struct literef * const ref)
{
  if (!rwlock_trylock_write(&(leaf->leaflock))) {
    litehole_park(ref);
    rwlock_lock_write(&(leaf->leaflock));
    litehole_resume(ref);
  }
}

  static void
liteleaf_lock_read(struct liteleaf * const leaf, struct literef * const ref)
{
  if (!rwlock_trylock_read(&(leaf->leaflock))) {
    litehole_park(ref);
    rwlock_lock_read(&(leaf->leaflock));
    litehole_resume(ref);
  }
}

  static void
liteleaf_unlock_write(struct liteleaf * const leaf)
{
  rwlock_unlock_write(&(leaf->leaflock));
}

  static void
liteleaf_unlock_read(struct liteleaf * const leaf)
{
  rwlock_unlock_read(&(leaf->leaflock));
}

  static void
litehmap_lock(struct litehole * const map, struct literef * const ref)
{
  if (!rwlock_trylock_write(&(map->metalock))) {
    litehole_park(ref);
    rwlock_lock_write(&(map->metalock));
    litehole_resume(ref);
  }
}

  static inline void
litehmap_unlock(struct litehole * const map)
{
  rwlock_unlock_write(&(map->metalock));
}
// }}} lock

// hmap-version {{{
  static inline struct litehmap *
litehmap_switch(struct litehole * const map, struct litehmap * const hmap)
{
  return (hmap == map->hmap2) ? (hmap + 1) : (hmap - 1);
}

  static inline struct litehmap *
litehmap_load(struct litehole * const map)
{
  return (struct litehmap *)atomic_load_explicit(&(map->hmap_ptr), MO_ACQUIRE);
}

  static inline void
litehmap_store(struct litehole * const map, struct litehmap * const hmap)
{
  atomic_store_explicit(&(map->hmap_ptr), (u64)hmap, MO_RELEASE);
}

  static inline u64
litehmap_version_load(const struct litehmap * const hmap)
{
  // no concurrent access
  return atomic_load_explicit(&(hmap->hv), MO_ACQUIRE);
}

  static inline void
litehmap_version_store(struct litehmap * const hmap, const u64 v)
{
  atomic_store_explicit(&(hmap->hv), v, MO_RELEASE);
}

  static inline u64
liteleaf_version_load(struct liteleaf * const leaf)
{
  return atomic_load_explicit(&(leaf->lv), MO_CONSUME);
}

  static inline void
liteleaf_version_store(struct liteleaf * const leaf, const u64 v)
{
  atomic_store_explicit(&(leaf->lv), v, MO_RELEASE);
}
// }}} hmap-version

// co {{{
  static inline void
litehole_qsbr_update_pause(struct literef * const ref, const u64 v)
{
  qsbr_update(&ref->qref, v);
#if defined(CORR)
  corr_yield();
#endif
}
// }}} co

// }}} helpers

// create {{{
// it's unsafe
  static bool
litehole_create_leaf0(struct litehole * const map)
{
  // create leaf of empty key
  struct kv * const anchor = malloc(sizeof(*anchor));
  if (anchor == NULL)
    return false;
  kv_dup2(kv_null(), anchor);

  struct liteleaf * const leaf0 = liteleaf_alloc(map, NULL, NULL, anchor);
  if (leaf0 == NULL) {
    free(anchor);
    return false;
  }

  map->leaf0 = leaf0;
  return true;
}

  struct litehole *
litehole_create(const struct kvmap_mm * const mm)
{
  struct litehole * const map = yalloc(sizeof(*map));
  if (map == NULL)
    return NULL;
  memset(map, 0, sizeof(*map));
  // mm
  map->mm = mm ? (*mm) : kvmap_mm_dup;

  // leaf slab
  map->slab_leaf = slab_create(sizeof(struct liteleaf), WH_SLABLEAF_SIZE);
  if (map->slab_leaf == NULL)
    goto fail;

  // qsbr
  map->qsbr = qsbr_create();
  if (map->qsbr == NULL)
    goto fail;

  // leaf0
  if (!litehole_create_leaf0(map))
    goto fail;

  struct liteleaf * const leaf0 = map->leaf0;

  // hmap
  for (u32 i = 0; i < 2; i++) {
    struct litehmap * const hmap = &map->hmap2[i];
    hmap->nalloc = 256;
    hmap->pairs = malloc(sizeof(*hmap->pairs) * 256);
    if (hmap->pairs == NULL)
      goto fail;

    hmap->pairs[0].leaf = leaf0;
    hmap->pairs[0].anchor = leaf0->anchor;
    hmap->nkeys = 1;
  }

  rwlock_init(&(map->metalock));
  litehmap_store(map, &map->hmap2[0]);
  return map;

fail:
  if (map->leaf0)
    liteleaf_free(map->slab_leaf, map->leaf0);

  if (map->qsbr)
    qsbr_destroy(map->qsbr);

  if (map->slab_leaf)
    slab_destroy(map->slab_leaf);

  for (u32 i = 0; i < 2; i++) {
    struct litehmap * const hmap = &map->hmap2[i];
    if (hmap->pairs)
      free(hmap->pairs);
  }

  free(map);
  return NULL;
}
// }}} create

// jump {{{
// return the index of leaf where anchor <= key < nextanchor
// seek_le
  static u64
litehmap_jump_i(const struct litehmap * const hmap, const struct kref * const key)
{
  u64 l = 0;
  u64 r = hmap->nkeys;
  while ((l + 1) < r) {
    const u64 m = (l + r) >> 1;
    const int cmp = kref_kv_compare(key, hmap->pairs[m].anchor);
    if (cmp < 0) {
      r = m;
    } else if (cmp > 0) {
      l = m;
    } else {
      return m;
    }
  }
  return l;
}

  static struct liteleaf *
litehole_jump_leaf(const struct litehmap * const hmap, const struct kref * const key)
{
  const u64 i = litehmap_jump_i(hmap, key);
  return hmap->pairs[i].leaf;
}

  static struct liteleaf *
litehole_jump_leaf_read(struct literef * const ref, const struct kref * const key)
{
  struct litehole * const map = ref->map;
#pragma nounroll
  do {
    const struct litehmap * const hmap = litehmap_load(map);
    const u64 v = litehmap_version_load(hmap);
    qsbr_update(&ref->qref, v);
    struct liteleaf * const leaf = litehole_jump_leaf(hmap, key);
#pragma nounroll
    do {
      if (rwlock_trylock_read_nr(&(leaf->leaflock), 64)) {
        if (liteleaf_version_load(leaf) <= v)
          return leaf;
        liteleaf_unlock_read(leaf);
        break;
      }
      // v1 is loaded before lv; if lv <= v, can update v1 without redo jump
      const u64 v1 = litehmap_version_load(litehmap_load(map));
      if (liteleaf_version_load(leaf) > v)
        break;
      litehole_qsbr_update_pause(ref, v1);
    } while (true);
  } while (true);
}

  static struct liteleaf *
litehole_jump_leaf_write(struct literef * const ref, const struct kref * const key)
{
  struct litehole * const map = ref->map;
#pragma nounroll
  do {
    const struct litehmap * const hmap = litehmap_load(map);
    const u64 v = litehmap_version_load(hmap);
    qsbr_update(&ref->qref, v);
    struct liteleaf * const leaf = litehole_jump_leaf(hmap, key);
#pragma nounroll
    do {
      if (rwlock_trylock_write_nr(&(leaf->leaflock), 64)) {
        if (liteleaf_version_load(leaf) <= v)
          return leaf;
        liteleaf_unlock_write(leaf);
        break;
      }
      // v1 is loaded before lv; if lv <= v, can update v1 without redo jump
      const u64 v1 = litehmap_version_load(litehmap_load(map));
      if (liteleaf_version_load(leaf) > v)
        break;
      litehole_qsbr_update_pause(ref, v1);
    } while (true);
  } while (true);
}
// }}} jump

// leaf {{{
// return WH_KPN when the key is not found
  static u32
liteleaf_match_i(const struct liteleaf * const leaf, const struct kref * const key)
{
  u32 l = 0;
  u32 r = leaf->nr_keys;
  while (l < r) {
    const u32 m = (l + r) >> 1;
    const int cmp = kref_kv_compare(key, leaf->kvs[m]);
    if (cmp < 0)
      r = m;
    else if (cmp > 0)
      l = m + 1;
    else
      return m;
  }
  return WH_KPN;
}

// the highest bit is set for match
  static u32
liteleaf_seek_ge(const struct liteleaf * const leaf, const struct kref * const key)
{
  u32 l = 0;
  u32 r = leaf->nr_keys;
  while (l < r) {
    const u32 m = (l + r) >> 1;
    const int cmp = kref_kv_compare(key, leaf->kvs[m]);
    if (cmp < 0)
      r = m;
    else if (cmp > 0)
      l = m + 1;
    else
      return m | (1u << 31);
  }
  return l;
}

  static struct kv *
liteleaf_update(struct liteleaf * const leaf, const u32 i, struct kv * const new)
{
  struct kv * const old = leaf->kvs[i];
  leaf->kvs[i] = new;
  return old;
}

  static void
liteleaf_insert(struct liteleaf * const leaf, const u32 i, struct kv * const new)
{
  memmove(&leaf->kvs[i+1], &leaf->kvs[i], sizeof(leaf->kvs[0]) * (leaf->nr_keys - i));
  leaf->kvs[i] = new;
}

  static struct liteleaf *
litehole_split_leaf(struct litehole * const map, struct liteleaf * const leaf1,
    const u32 i, struct kv * const new)
{
  debug_assert(leaf1->nr_keys == WH_KPN);
  struct kv * const anchor2 = kv_dup_key(leaf1->kvs[WH_MID]);
  if (anchor2 == NULL)
    return NULL;

  struct liteleaf * const leaf2 = liteleaf_alloc(map, leaf1, leaf1->next, anchor2);
  if (unlikely(leaf2 == NULL)) {
    free(anchor2);
    return NULL;
  }
  memmove(&leaf2->kvs[0], &leaf1->kvs[WH_MID], sizeof(leaf1->kvs[0]) * WH_MID);
  leaf1->nr_keys = WH_MID;
  leaf2->nr_keys = WH_MID;
  if (i <= WH_MID) {
    liteleaf_insert(leaf1, i, new);
  } else {
    liteleaf_insert(leaf2, i - WH_MID, new);
  }
  return leaf2;
}

  static struct kv *
liteleaf_remove(struct liteleaf * const leaf, const u32 i)
{
  struct kv * const kv = leaf->kvs[i];
  memmove(&leaf->kvs[i], &leaf->kvs[i+1], sizeof(leaf->kvs[0]) * (leaf->nr_keys - i - 1));
  leaf->nr_keys--;
  return kv;
}

  static bool
liteleaf_merge(struct liteleaf * const leaf1, struct liteleaf * const leaf2)
{
  debug_assert((leaf1->nr_keys + leaf2->nr_keys) < WH_KPN);
  memmove(&leaf1->kvs[leaf1->nr_keys], &leaf2->kvs[0], sizeof(leaf1->kvs[0]) * leaf2->nr_keys);
  leaf1->nr_keys += leaf2->nr_keys;
  leaf2->nr_keys = 0;
  return true;
}

  static void
liteleaf_split_undo(struct litehole * const map, struct liteleaf * const leaf1,
    struct liteleaf * const leaf2, const u32 i)
{
  if (i <= WH_MID) {
    liteleaf_remove(leaf1, i);
  } else {
    liteleaf_remove(leaf2, i - WH_MID);
  }
  debug_assert(leaf1->nr_keys == WH_MID);
  debug_assert(leaf2->nr_keys == WH_MID);
  liteleaf_merge(leaf1, leaf2);
  liteleaf_unlock_write(leaf2);
  liteleaf_free(map->slab_leaf, leaf2);
}
// }}} leaf

// get/probe {{{
  struct kv *
litehole_get(struct literef * const ref, const struct kref * const key, struct kv * const out)
{
  struct liteleaf * const leaf = litehole_jump_leaf_read(ref, key);
  const u32 i = liteleaf_match_i(leaf, key);
  struct kv * const tmp = (i < WH_KPN) ? ref->map->mm.out(leaf->kvs[i], out) : NULL;
  liteleaf_unlock_read(leaf);
  return tmp;
}

  struct kv *
whsafe_get(struct literef * const ref, const struct kref * const key, struct kv * const out)
{
  litehole_resume(ref);
  struct kv * const ret = litehole_get(ref, key, out);
  litehole_park(ref);
  return ret;
}
// }}} get/probe

// meta-split {{{
// return the index of leaf where anchor <= key < nextanchor
  static u64
litehmap_seek_ge(const struct litehmap * const hmap, const struct kv * const anchor)
{
  u64 l = 0;
  u64 r = hmap->nkeys;
  while (l < r) {
    const u64 m = (l + r) >> 1;
    const int cmp = kv_compare(anchor, hmap->pairs[m].anchor);
    if (cmp < 0) {
      r = m;
    } else if (cmp > 0) {
      l = m + 1;
    } else {
      return m;
    }
  }
  return l;
}

  static void
litemeta_split(struct litehmap * const hmap, struct liteleaf * const leaf)
{
  debug_assert(hmap->nalloc > hmap->nkeys);
  const u64 i = litehmap_seek_ge(hmap, leaf->anchor);
  memmove(&hmap->pairs[i+1], &hmap->pairs[i], sizeof(hmap->pairs[0]) * (hmap->nkeys - i));
  hmap->pairs[i].leaf = leaf;
  hmap->pairs[i].anchor = leaf->anchor;
  hmap->nkeys++;
}

// all locks will be released before returning
  static bool
litehole_split_meta(struct literef * const ref, struct liteleaf * const leaf2)
{
  struct litehole * const map = ref->map;
  // metalock
  litehmap_lock(map, ref);

  // check slab reserve
  const bool sr = litehole_hmap_reserve(map, 1);
  if (unlikely(!sr)) {
    litehmap_unlock(map);
    return false;
  }

  struct litehmap * const hmap0 = litehmap_load(map);
  struct litehmap * const hmap1 = litehmap_switch(map, hmap0);

  // link
  struct liteleaf * const leaf1 = leaf2->prev;
  leaf1->next = leaf2;
  if (leaf2->next)
    leaf2->next->prev = leaf2;

  // update versions
  const u64 v1 = litehmap_version_load(hmap0) + 1;
  liteleaf_version_store(leaf1, v1);
  liteleaf_version_store(leaf2, v1);
  litehmap_version_store(hmap1, v1);

  litemeta_split(hmap1, leaf2);

  qsbr_update(&ref->qref, v1);

  // switch hmap
  litehmap_store(map, hmap1);

  liteleaf_unlock_write(leaf1);
  liteleaf_unlock_write(leaf2);

  qsbr_wait(map->qsbr, v1);

  litemeta_split(hmap0, leaf2);

  litehmap_unlock(map);

  return true;
}

// all locks (metalock + leaflocks) will be released before returning
// leaf1->lock (write) is already taken
  static bool
litehole_split_insert(struct literef * const ref, struct liteleaf * const leaf1,
    const u32 i, struct kv * const new)
{
  struct liteleaf * const leaf2 = litehole_split_leaf(ref->map, leaf1, i, new);
  if (unlikely(leaf2 == NULL)) {
    liteleaf_unlock_write(leaf1);
    return false;
  }

  rwlock_lock_write(&(leaf2->leaflock));
  const bool rsm = litehole_split_meta(ref, leaf2);
  if (unlikely(!rsm)) {
    // undo insertion & merge; free leaf2
    liteleaf_split_undo(ref->map, leaf1, leaf2, i);
    liteleaf_unlock_write(leaf1);
  }
  return rsm;
}
// }}} meta-split

// meta-merge {{{
  static void
litemeta_merge(struct litehmap * const hmap, struct liteleaf * const leaf)
{
  const u64 i = litehmap_seek_ge(hmap, leaf->anchor);
  debug_assert(hmap->pairs[i].leaf == leaf);
  memmove(&hmap->pairs[i], &hmap->pairs[i+1], sizeof(hmap->pairs[0]) * (hmap->nkeys - i - 1));
  hmap->nkeys--;
}

// all locks (metalock + two leaflock) will be released before returning
// merge leaf2 to leaf1, removing all metadata to leaf2 and leaf2 itself
  static void
litehole_meta_merge(struct literef * const ref, struct liteleaf * const leaf1,
    struct liteleaf * const leaf2, const bool unlock_leaf1)
{
  debug_assert(leaf1->next == leaf2);
  debug_assert(leaf2->prev == leaf1);
  struct litehole * const map = ref->map;

  litehmap_lock(map, ref);

  struct litehmap * const hmap0 = litehmap_load(map);
  struct litehmap * const hmap1 = litehmap_switch(map, hmap0);
  const u64 v1 = litehmap_version_load(hmap0) + 1;

  leaf1->next = leaf2->next;
  if (leaf2->next)
    leaf2->next->prev = leaf1;

  liteleaf_version_store(leaf1, v1);
  liteleaf_version_store(leaf2, v1);
  litehmap_version_store(hmap1, v1);

  litemeta_merge(hmap1, leaf2);

  qsbr_update(&ref->qref, v1);

  // switch hmap
  litehmap_store(map, hmap1);

  if (unlock_leaf1)
    liteleaf_unlock_write(leaf1);
  liteleaf_unlock_write(leaf2);

  qsbr_wait(map->qsbr, v1);

  litemeta_merge(hmap0, leaf2);
  // leaf2 is now safe to be removed
  liteleaf_free(map->slab_leaf, leaf2);
  litehmap_unlock(map);
}

// caller must acquire leaf->wlock and next->wlock
// all locks will be released when this function returns
  static bool
litehole_meta_leaf_merge(struct literef * const ref, struct liteleaf * const leaf)
{
  struct liteleaf * const next = leaf->next;
  debug_assert(next);

  // double check
  if ((leaf->nr_keys + next->nr_keys) <= WH_KPN) {
    if (liteleaf_merge(leaf, next)) {
      litehole_meta_merge(ref, leaf, next, true);
      return true;
    }
  }
  // merge failed but it's fine
  liteleaf_unlock_write(leaf);
  liteleaf_unlock_write(next);
  return false;
}
// }}} meta-merge

// put {{{
  bool
litehole_put(struct literef * const ref, struct kv * const kv)
{
  // we always allocate a new item on SET
  // future optimizations may perform in-place update
  struct litehole * const map = ref->map;
  struct kv * const new = map->mm.in(kv, map->mm.priv);
  if (unlikely(new == NULL))
    return false;
  const struct kref kref = kv_kref(new);

  struct liteleaf * const leaf = litehole_jump_leaf_write(ref, &kref);
  // update
  const u32 im = liteleaf_seek_ge(leaf, &kref);
  const u32 i = im & WH_KPN_MASK;
  if (im >> 31) {
    struct kv * const old = liteleaf_update(leaf, i, new);
    liteleaf_unlock_write(leaf);
    map->mm.free(old, map->mm.priv);
    return true;
  }

  // insert
  if (likely(leaf->nr_keys < WH_KPN)) { // just insert
    liteleaf_insert(leaf, i, new);
    liteleaf_unlock_write(leaf);
    return true;
  }

  // split_insert changes hmap
  // all locks should be released in litehole_split_insert()
  const bool rsi = litehole_split_insert(ref, leaf, i, new);
  if (!rsi)
    map->mm.free(new, map->mm.priv);
  return rsi;
}

  bool
whsafe_put(struct literef * const ref, struct kv * const kv)
{
  litehole_resume(ref);
  const bool r = litehole_put(ref, kv);
  litehole_park(ref);
  return r;
}
// }}} put

// del {{{
  static void
litehole_del_try_merge(struct literef * const ref, struct liteleaf * const leaf)
{
  struct liteleaf * const next = leaf->next;
  if (next && ((leaf->nr_keys == 0) || ((leaf->nr_keys + next->nr_keys) < WH_KPN_MRG))) {
    // try merge, it may fail if size becomes larger after locking
    liteleaf_lock_write(next, ref);
    (void)litehole_meta_leaf_merge(ref, leaf);
    // locks are already released; immediately return
  } else {
    liteleaf_unlock_write(leaf);
  }
}

  bool
litehole_del(struct literef * const ref, const struct kref * const key)
{
  struct liteleaf * const leaf = litehole_jump_leaf_write(ref, key);
  const u32 im = liteleaf_match_i(leaf, key);
  if (im < WH_KPN) { // found
    struct kv * const kv = liteleaf_remove(leaf, im);
    litehole_del_try_merge(ref, leaf);
    debug_assert(kv);
    // free after releasing locks
    struct litehole * const map = ref->map;
    map->mm.free(kv, map->mm.priv);
    return true;
  } else {
    liteleaf_unlock_write(leaf);
    return false;
  }
}

  bool
whsafe_del(struct literef * const ref, const struct kref * const key)
{
  litehole_resume(ref);
  const bool r = litehole_del(ref, key);
  litehole_park(ref);
  return r;
}
// }}} del

// iter {{{
// safe iter: safe sort with read-lock acquired
// unsafe iter: allow concurrent seek/skip
  struct litehole_iter *
litehole_iter_create(struct literef * const ref)
{
  struct litehole_iter * const iter = malloc(sizeof(*iter));
  if (iter == NULL)
    return NULL;
  iter->ref = ref;
  iter->map = ref->map;
  iter->leaf = NULL;
  iter->is = 0;
  return iter;
}

  static void
litehole_iter_fix(struct litehole_iter * const iter)
{
  if (!litehole_iter_valid(iter))
    return;

  while (unlikely(iter->is >= iter->leaf->nr_keys)) {
    struct liteleaf * const next = iter->leaf->next;
    if (likely(next != NULL)) {
      struct literef * const ref = iter->ref;
      liteleaf_lock_read(next, ref);
      liteleaf_unlock_read(iter->leaf);

    } else {
      liteleaf_unlock_read(iter->leaf);
    }
    iter->leaf = next;
    iter->is = 0;
    if (!litehole_iter_valid(iter))
      return;
  }
}

  void
litehole_iter_seek(struct litehole_iter * const iter, const struct kref * const key)
{
  debug_assert(key);
  if (iter->leaf)
    liteleaf_unlock_read(iter->leaf);

  struct liteleaf * const leaf = litehole_jump_leaf_read(iter->ref, key);

  iter->leaf = leaf;
  iter->is = liteleaf_seek_ge(leaf, key);
  litehole_iter_fix(iter);
}

  void
whsafe_iter_seek(struct litehole_iter * const iter, const struct kref * const key)
{
  litehole_resume(iter->ref);
  litehole_iter_seek(iter, key);
}

  bool
litehole_iter_valid(struct litehole_iter * const iter)
{
  return iter->leaf != NULL;
}

  static struct kv *
litehole_iter_current(struct litehole_iter * const iter)
{
  if (litehole_iter_valid(iter)) {
    debug_assert(iter->is < iter->leaf->nr_keys);
    struct kv * const kv = iter->leaf->kvs[iter->is];
    return kv;
  }
  return NULL;
}

  struct kv *
litehole_iter_peek(struct litehole_iter * const iter, struct kv * const out)
{
  struct kv * const kv = litehole_iter_current(iter);
  if (kv) {
    struct kv * const ret = iter->map->mm.out(kv, out);
    return ret;
  }
  return NULL;
}

  bool
litehole_iter_kref(struct litehole_iter * const iter, struct kref * const kref)
{
  struct kv * const kv = litehole_iter_current(iter);
  if (kv) {
    kref_ref_kv(kref, kv);
    return true;
  }
  return false;
}

  bool
litehole_iter_kvref(struct litehole_iter * const iter, struct kvref * const kvref)
{
  struct kv * const kv = litehole_iter_current(iter);
  if (kv) {
    kvref_ref_kv(kvref, kv);
    return true;
  }
  return false;
}

  void
litehole_iter_skip1(struct litehole_iter * const iter)
{
  if (litehole_iter_valid(iter)) {
    iter->is++;
    litehole_iter_fix(iter);
  }
}

  void
litehole_iter_skip(struct litehole_iter * const iter, const u32 nr)
{
  u32 todo = nr;
  while (todo && litehole_iter_valid(iter)) {
    const u32 cap = iter->leaf->nr_keys - iter->is;
    const u32 nskip = (cap < todo) ? cap : todo;
    iter->is += nskip;
    litehole_iter_fix(iter);
    todo -= nskip;
  }
}

  struct kv *
litehole_iter_next(struct litehole_iter * const iter, struct kv * const out)
{
  struct kv * const ret = litehole_iter_peek(iter, out);
  litehole_iter_skip1(iter);
  return ret;
}

  bool
litehole_iter_inp(struct litehole_iter * const iter, kv_inp_func uf, void * const priv)
{
  struct kv * const kv = litehole_iter_current(iter);
  uf(kv, priv); // call uf even if (kv == NULL)
  return kv != NULL;
}

  void
litehole_iter_park(struct litehole_iter * const iter)
{
  if (iter->leaf) {
    liteleaf_unlock_read(iter->leaf);
    iter->leaf = NULL;
  }
}

  void
whsafe_iter_park(struct litehole_iter * const iter)
{
  litehole_iter_park(iter);
  litehole_park(iter->ref);
}

  void
litehole_iter_destroy(struct litehole_iter * const iter)
{
  if (iter->leaf)
    liteleaf_unlock_read(iter->leaf);
  free(iter);
}

  void
whsafe_iter_destroy(struct litehole_iter * const iter)
{
  litehole_park(iter->ref);
  litehole_iter_destroy(iter);
}
// }}} iter

// misc {{{
  struct literef *
litehole_ref(struct litehole * const map)
{
  struct literef * const ref = malloc(sizeof(*ref));
  if (ref == NULL)
    return NULL;
  ref->map = map;
  if (qsbr_register(map->qsbr, &(ref->qref)) == false) {
    free(ref);
    return NULL;
  }
  return ref;
}

  struct literef *
whsafe_ref(struct litehole * const map)
{
  struct literef * const ref = litehole_ref(map);
  if (ref)
    litehole_park(ref);
  return ref;
}

  struct litehole *
litehole_unref(struct literef * const ref)
{
  struct litehole * const map = ref->map;
  qsbr_unregister(map->qsbr, &(ref->qref));
  free(ref);
  return map;
}

  inline void
litehole_park(struct literef * const ref)
{
  qsbr_park(&(ref->qref));
}

  inline void
litehole_resume(struct literef * const ref)
{
  qsbr_resume(&(ref->qref));
}

  inline void
litehole_refresh_qstate(struct literef * const ref)
{
  qsbr_update(&(ref->qref), litehmap_version_load(litehmap_load(ref->map)));
}

  static void
litehole_clean_hmap(struct litehole * const map)
{
  for (u32 x = 0; x < 2; x++) {
    map->hmap2[x].nkeys = 0;
  }
}

  static void
litehole_free_leaf_keys(struct litehole * const map, struct liteleaf * const leaf)
{
  const u32 nr = leaf->nr_keys;
  for (u32 i = 0; i < nr; i++) {
    void * const curr = leaf->kvs[i];
    debug_assert(curr);
    map->mm.free(curr, map->mm.priv);
  }
  free(leaf->anchor);
}

  static void
litehole_clean_helper(struct litehole * const map)
{
  litehole_clean_hmap(map);
  for (struct liteleaf * leaf = map->leaf0; leaf; leaf = leaf->next)
    litehole_free_leaf_keys(map, leaf);
  slab_free_all(map->slab_leaf);
  map->leaf0 = NULL;
}

// unsafe
  void
litehole_clean(struct litehole * const map)
{
  litehole_clean_helper(map);
  litehole_create_leaf0(map);
}

  void
litehole_destroy(struct litehole * const map)
{
  litehole_clean_helper(map);
  for (u32 i = 0; i < 2; i++) {
    struct litehmap * const hmap = &map->hmap2[i];
    if (hmap->pairs)
      free(hmap->pairs);
  }
  qsbr_destroy(map->qsbr);
  slab_destroy(map->slab_leaf);
  free(map);
}
// }}} misc

// vim:fdm=marker
