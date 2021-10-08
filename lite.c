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
#include "wh.h"
// }}} headers

// def {{{
#define WH_HMAPINIT_SIZE ((1u << 12)) // 10: 16KB/64KB  12: 64KB/256KB  14: 256KB/1MB
#define WH_SLABMETA_SIZE ((1lu << 21)) // 2MB

#ifndef HEAPCHECKING
#define WH_SLABLEAF_SIZE ((1lu << 21)) // 2MB is ok
#else
#define WH_SLABLEAF_SIZE ((1lu << 21)) // 2MB for valgrind
#endif

#define WH_KPN ((128u)) // keys per node; power of 2
#define WH_KPN_MASK ((WH_KPN - 1))
#define WH_HDIV (((1u << 16)) / WH_KPN)
#define WH_MID ((WH_KPN >> 1)) // ideal cut point for split, the closer the better
#define WH_BKT_NR ((8))
#define WH_KPN2 ((WH_KPN + WH_KPN))

#define WH_KPN_MRG (((WH_KPN + WH_MID) >> 1 )) // 3/4

// FO is fixed at 256. Don't change it
#define WH_FO  ((256u)) // index fan-out
// number of bits in a bitmap
#define WH_BMNR ((WH_FO >> 6)) // number of u64
// }}} def

// struct {{{
struct wormleaf {
  // first line
  rwlock leaflock;
  u32 padding;
  au64 lv; // version (dont use the first u64)
  struct wormleaf * prev; // prev leaf
  struct wormleaf * next; // next leaf
  struct kv * anchor;

  u32 nr_keys;
  u32 reserved[5];

  struct kv * kvs[WH_KPN];
};

struct wormhmap {
  au64 hv;
  u64 padding[7];

  u64 nkeys;
  u64 nalloc;
  struct kv * pbuf;

  struct {
    struct wormleaf * leaf;
    struct kv * anchor;
  } * pairs;
  u64 padding1[4];
};

struct wormhole {
  // 1 line
  union {
    volatile au64 hmap_ptr; // safe
    struct wormhmap * hmap; // unsafe
  };
  u64 padding0[6];
  struct wormleaf * leaf0; // usually not used
  // 1 line
  struct kvmap_mm mm;
  struct qsbr * qsbr;
  struct slab * slab_leaf;
  struct kv * pbuf;
  u32 padding1[2];
  // 2 lines
  struct wormhmap hmap2[2];
  // fifth line
  rwlock metalock;
  u32 padding2[15];
};

struct wormhole_iter {
  struct wormref * ref; // safe-iter only
  struct wormhole * map;
  struct wormleaf * leaf;
  u32 is;
};

struct wormref {
  struct wormhole * map;
  struct qsbr_ref qref;
};
// }}} struct

// helpers {{{

// alloc {{{
  static inline struct kv *
wormhole_alloc_akey(const size_t klen)
{
#ifdef ALLOCFAIL
  if (alloc_fail())
    return NULL;
#endif
  return malloc(sizeof(struct kv) + klen);
}

  static inline void
wormhole_free_akey(struct kv * const akey)
{
  free(akey);
}

  static struct wormleaf *
wormleaf_alloc(struct wormhole * const map, struct wormleaf * const prev,
    struct wormleaf * const next, struct kv * const anchor)
{
  struct wormleaf * const leaf = slab_alloc_safe(map->slab_leaf);
  if (leaf == NULL)
    return NULL;

  rwlock_init(&(leaf->leaflock));

  // keep the old version; new version will be assigned by split functions
  //leaf->lv = 0;

  leaf->prev = prev;
  leaf->next = next;
  leaf->anchor = anchor;

  leaf->nr_keys = 0;

  // hs requires zero init.
  memset(leaf->kvs, 0, sizeof(leaf->kvs[0]) * WH_KPN);
  return leaf;
}

  static void
wormleaf_free(struct slab * const slab, struct wormleaf * const leaf)
{
  debug_assert(leaf->leaflock.opaque == 0);
  wormhole_free_akey(leaf->anchor);
  slab_free_safe(slab, leaf);
}

  static inline bool
wormhole_hmap_reserve(struct wormhole * const map, const u32 nr)
{
#ifdef ALLOCFAIL
  if (alloc_fail())
    return false;
#endif
  for (u32 i = 0; i < 2; i++) {
    struct wormhmap * const hmap = &map->hmap2[i];
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
wormleaf_lock_write(struct wormleaf * const leaf, struct wormref * const ref)
{
  if (!rwlock_trylock_write(&(leaf->leaflock))) {
    wormhole_park(ref);
    rwlock_lock_write(&(leaf->leaflock));
    wormhole_resume(ref);
  }
}

  static void
wormleaf_lock_read(struct wormleaf * const leaf, struct wormref * const ref)
{
  if (!rwlock_trylock_read(&(leaf->leaflock))) {
    wormhole_park(ref);
    rwlock_lock_read(&(leaf->leaflock));
    wormhole_resume(ref);
  }
}

  static void
wormleaf_unlock_write(struct wormleaf * const leaf)
{
  rwlock_unlock_write(&(leaf->leaflock));
}

  static void
wormleaf_unlock_read(struct wormleaf * const leaf)
{
  rwlock_unlock_read(&(leaf->leaflock));
}

  static void
wormhmap_lock(struct wormhole * const map, struct wormref * const ref)
{
  if (!rwlock_trylock_write(&(map->metalock))) {
    wormhole_park(ref);
    rwlock_lock_write(&(map->metalock));
    wormhole_resume(ref);
  }
}

  static inline void
wormhmap_unlock(struct wormhole * const map)
{
  rwlock_unlock_write(&(map->metalock));
}
// }}} lock

// hmap-version {{{
  static inline struct wormhmap *
wormhmap_switch(struct wormhole * const map, struct wormhmap * const hmap)
{
  return (hmap == map->hmap2) ? (hmap + 1) : (hmap - 1);
}

  static inline struct wormhmap *
wormhmap_load(struct wormhole * const map)
{
  return (struct wormhmap *)atomic_load_explicit(&(map->hmap_ptr), MO_ACQUIRE);
}

  static inline void
wormhmap_store(struct wormhole * const map, struct wormhmap * const hmap)
{
  atomic_store_explicit(&(map->hmap_ptr), (u64)hmap, MO_RELEASE);
}

  static inline u64
wormhmap_version_load(const struct wormhmap * const hmap)
{
  // no concurrent access
  return atomic_load_explicit(&(hmap->hv), MO_ACQUIRE);
}

  static inline void
wormhmap_version_store(struct wormhmap * const hmap, const u64 v)
{
  atomic_store_explicit(&(hmap->hv), v, MO_RELEASE);
}

  static inline u64
wormleaf_version_load(struct wormleaf * const leaf)
{
  return atomic_load_explicit(&(leaf->lv), MO_CONSUME);
}

  static inline void
wormleaf_version_store(struct wormleaf * const leaf, const u64 v)
{
  atomic_store_explicit(&(leaf->lv), v, MO_RELEASE);
}
// }}} hmap-version

// co {{{
  static inline bool
wormhole_kref_kv_match(const struct kref * const key, const struct kv * const curr)
{
#if defined(CORR)
  const u8 * const ptr = (typeof(ptr))curr;
  cpu_prefetch0(ptr);
  cpu_prefetch0(ptr + 64);
  if (key->len > 56) {
    cpu_prefetch0(ptr + 128);
    cpu_prefetch0(ptr + 192);
  }
  corr_yield();
#endif
  return kref_kv_match(key, curr);
}

  static inline void
wormhole_qsbr_update_pause(struct wormref * const ref, const u64 v)
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
wormhole_create_leaf0(struct wormhole * const map)
{
  // create leaf of empty key
  struct kv * const anchor = wormhole_alloc_akey(0);
  if (anchor == NULL)
    return false;
  kv_dup2(kv_null(), anchor);

  struct wormleaf * const leaf0 = wormleaf_alloc(map, NULL, NULL, anchor);
  if (leaf0 == NULL) {
    wormhole_free_akey(anchor);
    return false;
  }

  map->leaf0 = leaf0;
  return true;
}

  static struct wormhole *
wormhole_create_internal(const struct kvmap_mm * const mm, const u32 nh)
{
  struct wormhole * const map = yalloc(sizeof(*map));
  if (map == NULL)
    return NULL;
  memset(map, 0, sizeof(*map));
  // mm
  map->mm = mm ? (*mm) : kvmap_mm_dup;

  // pbuf for meta-merge
  map->pbuf = yalloc(1lu << 16); // 64kB
  if (map->pbuf == NULL)
    goto fail;

  // leaf slab
  map->slab_leaf = slab_create(sizeof(struct wormleaf), WH_SLABLEAF_SIZE);
  if (map->slab_leaf == NULL)
    goto fail;

  // qsbr
  map->qsbr = qsbr_create();
  if (map->qsbr == NULL)
    goto fail;

  // leaf0
  if (!wormhole_create_leaf0(map))
    goto fail;

  // hmap
  for (u32 i = 0; i < nh; i++) {
    struct wormhmap * const hmap = &map->hmap2[i];
    hmap->nalloc = 256;
    hmap->pbuf = map->pbuf;
    hmap->pairs = malloc(sizeof(*hmap->pairs) * 256);
    if (hmap->pairs == NULL)
      goto fail;

    hmap->pairs[0].leaf = leaf0;
    hmap->pairs[0].anchor = leaf0->anchor;
    hmap->nkeys = 1;
  }

  rwlock_init(&(map->metalock));
  wormhmap_store(map, &map->hmap2[0]);
  return map;

fail:
  if (leaf0)
    wormleaf_free(map->slab_leaf, leaf0);

  if (map->qsbr)
    qsbr_destroy(map->qsbr);

  if (map->slab_leaf)
    slab_destroy(map->slab_leaf);

  for (u32 i = 0; i < nh; i++) {
    struct wormhmap * const hmap = &map->hmap2[i];
    if (hmap->pairs)
      free(hmap->pairs);
  }

  if (map->pbuf)
    free(map->pbuf);

  free(map);
  return NULL;
}

  struct wormhole *
wormhole_create(const struct kvmap_mm * const mm)
{
  return wormhole_create_internal(mm, 2);
}

  struct wormhole *
whunsafe_create(const struct kvmap_mm * const mm)
{
  return wormhole_create_internal(mm, 1);
}
// }}} create

// jump {{{
// return the index of leaf where anchor <= key < nextanchor
  static u64
wormhmap_jump_i(const struct wormhmap * const hmap, const struct kref * const key)
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

  static struct wormleaf *
wormhole_jump_leaf(const struct wormhmap * const hmap, const struct kref * const key)
{
  const u64 i = wormhmap_jump_i(hmap, key);
  return hmap->pairs[i].leaf;
}

  static struct wormleaf *
wormhole_jump_leaf_read(struct wormref * const ref, const struct kref * const key)
{
  struct wormhole * const map = ref->map;
#pragma nounroll
  do {
    const struct wormhmap * const hmap = wormhmap_load(map);
    const u64 v = wormhmap_version_load(hmap);
    qsbr_update(&ref->qref, v);
    struct wormleaf * const leaf = wormhole_jump_leaf(hmap, key);
#pragma nounroll
    do {
      if (rwlock_trylock_read_nr(&(leaf->leaflock), 64)) {
        if (wormleaf_version_load(leaf) <= v)
          return leaf;
        wormleaf_unlock_read(leaf);
        break;
      }
      // v1 is loaded before lv; if lv <= v, can update v1 without redo jump
      const u64 v1 = wormhmap_version_load(wormhmap_load(map));
      if (wormleaf_version_load(leaf) > v)
        break;
      wormhole_qsbr_update_pause(ref, v1);
    } while (true);
  } while (true);
}

  static struct wormleaf *
wormhole_jump_leaf_write(struct wormref * const ref, const struct kref * const key)
{
  struct wormhole * const map = ref->map;
#pragma nounroll
  do {
    const struct wormhmap * const hmap = wormhmap_load(map);
    const u64 v = wormhmap_version_load(hmap);
    qsbr_update(&ref->qref, v);
    struct wormleaf * const leaf = wormhole_jump_leaf(hmap, key);
#pragma nounroll
    do {
      if (rwlock_trylock_write_nr(&(leaf->leaflock), 64)) {
        if (wormleaf_version_load(leaf) <= v)
          return leaf;
        wormleaf_unlock_write(leaf);
        break;
      }
      // v1 is loaded before lv; if lv <= v, can update v1 without redo jump
      const u64 v1 = wormhmap_version_load(wormhmap_load(map));
      if (wormleaf_version_load(leaf) > v)
        break;
      wormhole_qsbr_update_pause(ref, v1);
    } while (true);
  } while (true);
}
// }}} jump

// leaf {{{
// return WH_KPN when the key is not found
  const u32
wormleaf_match_i(const struct wormleaf * const leaf, const struct kref * const key)
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
  const u32
wormleaf_seek_ge(const struct wormleaf * const leaf, const struct kref * const key)
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
wormleaf_update(struct wormleaf * const leaf, const u32 i, struct kv * const new)
{
  struct kv * const old = leaf->kvs[i];
  leaf->kvs[i] = new;
  return old;
}

  static void
wormleaf_insert(struct wormleaf * const leaf, const u32 i, struct kv * const new)
{
  memmove(&leaf->kvs[i+1], &leaf->kvs[i], sizeof(leaf->kvs[0]) * (leaf->nr_keys - i));
  leaf->kvs[i] = new;
}

// create an anchor for leaf-split
  static struct kv *
wormhole_split_alloc_anchor(const struct kv * const key1, const struct kv * const key2)
{
  const u32 alen = kv_key_lcp(key1, key2) + 1;
  debug_assert(alen <= key2->klen);

  struct kv * const anchor = wormhole_alloc_akey(alen);
  if (anchor)
    kv_refill(anchor, key2->kv, alen, NULL, 0);
  return anchor;
}

  static struct wormleaf *
wormhole_split_leaf(struct wormhole * const map, struct wormleaf * const leaf1,
    const u32 i, struct kv * const new)
{
  debug_assert(leaf1->nr_keys == WH_KPN);
  struct kv * const anchor2 = wormhole_split_alloc_anchor(leaf1->kvs[WH_MID-1], leaf1->kvs[WH_MID]);
  if (anchor2 == NULL)
    return NULL;

  struct wormleaf * const leaf2 = wormleaf_alloc(map, leaf1, leaf1->next, anchor2);
  if (unlikely(leaf2 == NULL)) {
    wormhole_free_akey(anchor2);
    return NULL;
  }
  memmove(&leaf2->kvs[0], &leaf1->kvs[WH_MID], sizeof(leaf1->kvs[0]) * WH_MID);
  leaf1->nr_keys = WH_MID;
  leaf2->nr_keys = WH_MID;
  if (i <= WH_MID) {
    wormleaf_insert(leaf1, i, new);
  } else {
    wormleaf_insert(leaf2, i - WH_MID, new);
  }
}
// }}} leaf

// get/probe {{{
  struct kv *
wormhole_get(struct wormref * const ref, const struct kref * const key, struct kv * const out)
{
  struct wormleaf * const leaf = wormhole_jump_leaf_read(ref, key);
  const u32 i = wormleaf_match_i(leaf, key);
  struct kv * const tmp = (i < WH_KPN) ? ref->map->mm.out(wormleaf_kv_at_ih(leaf, i), out) : NULL;
  wormleaf_unlock_read(leaf);
  return tmp;
}

  struct kv *
whsafe_get(struct wormref * const ref, const struct kref * const key, struct kv * const out)
{
  wormhole_resume(ref);
  struct kv * const ret = wormhole_get(ref, key, out);
  wormhole_park(ref);
  return ret;
}

  struct kv *
whunsafe_get(struct wormhole * const map, const struct kref * const key, struct kv * const out)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, key);
  const u32 i = wormleaf_match_i(leaf, key);
  return (i < WH_KPN) ? map->mm.out(wormleaf_kv_at_ih(leaf, i), out) : NULL;
}

  bool
wormhole_probe(struct wormref * const ref, const struct kref * const key)
{
  struct wormleaf * const leaf = wormhole_jump_leaf_read(ref, key);
  const u32 i = wormleaf_match_i(leaf, key);
  wormleaf_unlock_read(leaf);
  return i < WH_KPN;
}

  bool
whsafe_probe(struct wormref * const ref, const struct kref * const key)
{
  wormhole_resume(ref);
  const bool r = wormhole_probe(ref, key);
  wormhole_park(ref);
  return r;
}

  bool
whunsafe_probe(struct wormhole * const map, const struct kref * const key)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, key);
  return wormleaf_match_i(leaf, key) < WH_KPN;
}
// }}} get/probe

// meta-split {{{
// all locks will be released before returning
  static bool
wormhole_split_meta(struct wormref * const ref, struct wormleaf * const leaf2)
{
  struct wormhole * const map = ref->map;
  // metalock
  wormhmap_lock(map, ref);

  // check slab reserve
  const bool sr = wormhole_hmap_reserve(map, 1);
  if (unlikely(!sr)) {
    wormhmap_unlock(map);
    return false;
  }

  struct wormhmap * const hmap0 = wormhmap_load(map);
  struct wormhmap * const hmap1 = wormhmap_switch(map, hmap0);

  // link
  struct wormleaf * const leaf1 = leaf2->prev;
  leaf1->next = leaf2;
  if (leaf2->next)
    leaf2->next->prev = leaf2;

  // update versions
  const u64 v1 = wormhmap_version_load(hmap0) + 1;
  wormleaf_version_store(leaf1, v1);
  wormleaf_version_store(leaf2, v1);
  wormhmap_version_store(hmap1, v1);

  wormmeta_split(hmap1, leaf2, mkey);

  qsbr_update(&ref->qref, v1);

  // switch hmap
  wormhmap_store(map, hmap1);

  wormleaf_unlock_write(leaf1);
  wormleaf_unlock_write(leaf2);

  qsbr_wait(map->qsbr, v1);

  wormmeta_split(hmap0, leaf2, mkey);

  wormhmap_unlock(map);

  return true;
}

// all locks (metalock + leaflocks) will be released before returning
// leaf1->lock (write) is already taken
  static bool
wormhole_split_insert(struct wormref * const ref, struct wormleaf * const leaf1,
    const u32 i, struct kv * const new)
{
  struct wormleaf * const leaf2 = wormhole_split_leaf(ref->map, leaf1, i, new);
  if (unlikely(leaf2 == NULL)) {
    wormleaf_unlock_write(leaf1);
    return false;
  }

  rwlock_lock_write(&(leaf2->leaflock));
  const bool rsm = wormhole_split_meta(ref, leaf2);
  if (unlikely(!rsm)) {
    // undo insertion & merge; free leaf2
    wormleaf_split_undo(ref->map, leaf1, leaf2, new);
    wormleaf_unlock_write(leaf1);
  }
  return rsm;
}

  static bool
whunsafe_split_meta(struct wormhole * const map, struct wormleaf * const leaf2)
{
  const bool sr = wormhole_hmap_reserve(map, 1);
  if (unlikely(!sr)) {
    wormhmap_unlock(map);
    return false;
  }

  // link
  leaf2->prev->next = leaf2;
  if (leaf2->next)
    leaf2->next->prev = leaf2;

  for (u32 i = 0; i < 2; i++)
    if (map->hmap2[i].pmap)
      wormmeta_split(&(map->hmap2[i]), leaf2, mkey);
  return true;
}

  static bool
whunsafe_split_insert(struct wormhole * const map, struct wormleaf * const leaf1,
    struct kv * const new)
{
  struct wormleaf * const leaf2 = wormhole_split_leaf(map, leaf1, new);
  if (unlikely(leaf2 == NULL))
    return false;

  const bool rsm = whunsafe_split_meta(map, leaf2);
  if (unlikely(!rsm))  // undo insertion, merge, free leaf2
    wormleaf_split_undo(map, leaf1, leaf2, new);

  return rsm;
}
// }}} meta-split

// meta-merge {{{
// all locks (metalock + two leaflock) will be released before returning
// merge leaf2 to leaf1, removing all metadata to leaf2 and leaf2 itself
  static void
wormhole_meta_merge(struct wormref * const ref, struct wormleaf * const leaf1,
    struct wormleaf * const leaf2, const bool unlock_leaf1)
{
  debug_assert(leaf1->next == leaf2);
  debug_assert(leaf2->prev == leaf1);
  struct wormhole * const map = ref->map;

  wormhmap_lock(map, ref);

  struct wormhmap * const hmap0 = wormhmap_load(map);
  struct wormhmap * const hmap1 = wormhmap_switch(map, hmap0);
  const u64 v1 = wormhmap_version_load(hmap0) + 1;

  leaf1->next = leaf2->next;
  if (leaf2->next)
    leaf2->next->prev = leaf1;

  wormleaf_version_store(leaf1, v1);
  wormleaf_version_store(leaf2, v1);
  wormhmap_version_store(hmap1, v1);

  wormmeta_merge(hmap1, leaf2);

  qsbr_update(&ref->qref, v1);

  // switch hmap
  wormhmap_store(map, hmap1);

  if (unlock_leaf1)
    wormleaf_unlock_write(leaf1);
  wormleaf_unlock_write(leaf2);

  qsbr_wait(map->qsbr, v1);

  wormmeta_merge(hmap0, leaf2);
  // leaf2 is now safe to be removed
  wormleaf_free(map->slab_leaf, leaf2);
  wormhmap_unlock(map);
}

// caller must acquire leaf->wlock and next->wlock
// all locks will be released when this function returns
  static bool
wormhole_meta_leaf_merge(struct wormref * const ref, struct wormleaf * const leaf)
{
  struct wormleaf * const next = leaf->next;
  debug_assert(next);

  // double check
  if ((leaf->nr_keys + next->nr_keys) <= WH_KPN) {
    if (wormleaf_merge(leaf, next)) {
      wormhole_meta_merge(ref, leaf, next, true);
      return true;
    }
  }
  // merge failed but it's fine
  wormleaf_unlock_write(leaf);
  wormleaf_unlock_write(next);
  return false;
}

  static void
whunsafe_meta_leaf_merge(struct wormhole * const map, struct wormleaf * const leaf1,
    struct wormleaf * const leaf2)
{
  debug_assert(leaf1->next == leaf2);
  debug_assert(leaf2->prev == leaf1);
  if (!wormleaf_merge(leaf1, leaf2))
    return;

  leaf1->next = leaf2->next;
  if (leaf2->next)
    leaf2->next->prev = leaf1;
  for (u32 i = 0; i < 2; i++)
    if (map->hmap2[i].pairs)
      wormmeta_merge(&(map->hmap2[i]), leaf2);
  wormleaf_free(map->slab_leaf, leaf2);
}
// }}} meta-merge

// put {{{
  bool
wormhole_put(struct wormref * const ref, struct kv * const kv)
{
  // we always allocate a new item on SET
  // future optimizations may perform in-place update
  struct wormhole * const map = ref->map;
  struct kv * const new = map->mm.in(kv, map->mm.priv);
  if (unlikely(new == NULL))
    return false;
  const struct kref kref = kv_kref(new);

  struct wormleaf * const leaf = wormhole_jump_leaf_write(ref, &kref);
  // update
  const u32 im = wormleaf_seek_ge(leaf, &kref);
  const u32 i = im & WH_KPN_MASK;
  if (im >> 31) {
    struct kv * const old = wormleaf_update(leaf, i, new);
    wormleaf_unlock_write(leaf);
    map->mm.free(old, map->mm.priv);
    return true;
  }

  // insert
  if (likely(leaf->nr_keys < WH_KPN)) { // just insert
    wormleaf_insert(leaf, i, new);
    wormleaf_unlock_write(leaf);
    return true;
  }

  // split_insert changes hmap
  // all locks should be released in wormhole_split_insert()
  const bool rsi = wormhole_split_insert(ref, leaf, i, new);
  if (!rsi)
    map->mm.free(new, map->mm.priv);
  return rsi;
}

  bool
whsafe_put(struct wormref * const ref, struct kv * const kv)
{
  wormhole_resume(ref);
  const bool r = wormhole_put(ref, kv);
  wormhole_park(ref);
  return r;
}

  bool
whunsafe_put(struct wormhole * const map, struct kv * const kv)
{
  struct kv * const new = map->mm.in(kv, map->mm.priv);
  if (unlikely(new == NULL))
    return false;
  const struct kref kref = kv_kref(new);

  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, &kref);
  // update
  const u32 im = wormleaf_match_hs(leaf, &kref);
  if (im < WH_KPN) { // overwrite
    struct kv * const old = wormleaf_update(leaf, im, new);
    map->mm.free(old, map->mm.priv);
    return true;
  }

  // insert
  if (likely(leaf->nr_keys < WH_KPN)) { // just insert
    wormleaf_insert(leaf, new);
    return true;
  }

  // split_insert changes hmap
  const bool rsi = whunsafe_split_insert(map, leaf, new);
  if (!rsi)
    map->mm.free(new, map->mm.priv);
  return rsi;
}

  bool
wormhole_merge(struct wormref * const ref, const struct kref * const kref,
    kv_merge_func uf, void * const priv)
{
  struct wormhole * const map = ref->map;
  struct wormleaf * const leaf = wormhole_jump_leaf_write(ref, kref);
  // update
  const u32 im = wormleaf_match_hs(leaf, kref);
  if (im < WH_KPN) { // update
    struct kv * const kv0 = wormleaf_kv_at_ih(leaf, im);
    struct kv * const kv = uf(kv0, priv);
    if ((kv == kv0) || (kv == NULL)) { // no replacement
      wormleaf_unlock_write(leaf);
      return true;
    }

    struct kv * const new = map->mm.in(kv, map->mm.priv);
    if (unlikely(new == NULL)) { // mm error
      wormleaf_unlock_write(leaf);
      return false;
    }

    struct kv * const old = wormleaf_update(leaf, im, new);
    wormleaf_unlock_write(leaf);
    map->mm.free(old, map->mm.priv);
    return true;
  }

  struct kv * const kv = uf(NULL, priv);
  if (kv == NULL) { // nothing to be inserted
    wormleaf_unlock_write(leaf);
    return true;
  }

  struct kv * const new = map->mm.in(kv, map->mm.priv);
  if (unlikely(new == NULL)) { // mm error
    wormleaf_unlock_write(leaf);
    return false;
  }

  // insert
  if (likely(leaf->nr_keys < WH_KPN)) { // just insert
    wormleaf_insert(leaf, new);
    wormleaf_unlock_write(leaf);
    return true;
  }

  // split_insert changes hmap
  // all locks should be released in wormhole_split_insert()
  const bool rsi = wormhole_split_insert(ref, leaf, i, new);
  if (!rsi)
    map->mm.free(new, map->mm.priv);
  return rsi;
}

  bool
whsafe_merge(struct wormref * const ref, const struct kref * const kref,
    kv_merge_func uf, void * const priv)
{
  wormhole_resume(ref);
  const bool r = wormhole_merge(ref, kref, uf, priv);
  wormhole_park(ref);
  return r;
}

  bool
whunsafe_merge(struct wormhole * const map, const struct kref * const kref,
    kv_merge_func uf, void * const priv)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, kref);
  // update
  const u32 im = wormleaf_match_hs(leaf, kref);
  if (im < WH_KPN) { // update
    struct kv * const kv0 = wormleaf_kv_at_ih(leaf, im);
    struct kv * const kv = uf(kv0, priv);
    if ((kv == kv0) || (kv == NULL))
      return true;

    struct kv * const new = map->mm.in(kv, map->mm.priv);
    if (unlikely(new == NULL))
      return false;

    struct kv * const old = wormleaf_update(leaf, im, new);
    map->mm.free(old, map->mm.priv);
    return true;
  }

  struct kv * const kv = uf(NULL, priv);
  if (kv == NULL) // nothing to be inserted
    return true;

  struct kv * const new = map->mm.in(kv, map->mm.priv);
  if (unlikely(new == NULL)) // mm error
    return false;

  // insert
  if (likely(leaf->nr_keys < WH_KPN)) { // just insert
    wormleaf_insert(leaf, new);
    return true;
  }

  // split_insert changes hmap
  const bool rsi = whunsafe_split_insert(map, leaf, new);
  if (!rsi)
    map->mm.free(new, map->mm.priv);
  return rsi;
}
// }}} put

// inplace {{{
  bool
wormhole_inpr(struct wormref * const ref, const struct kref * const key,
    kv_inp_func uf, void * const priv)
{
  struct wormleaf * const leaf = wormhole_jump_leaf_read(ref, key);
  const u32 im = wormleaf_match_hs(leaf, key);
  if (im < WH_KPN) {
    uf(wormleaf_kv_at_ih(leaf, im), priv);
    wormleaf_unlock_read(leaf);
    return true;
  } else {
    uf(NULL, priv);
    wormleaf_unlock_read(leaf);
    return false;
  }
}

  bool
wormhole_inpw(struct wormref * const ref, const struct kref * const key,
    kv_inp_func uf, void * const priv)
{
  struct wormleaf * const leaf = wormhole_jump_leaf_write(ref, key);
  const u32 im = wormleaf_match_hs(leaf, key);
  if (im < WH_KPN) {
    uf(wormleaf_kv_at_ih(leaf, im), priv);
    wormleaf_unlock_write(leaf);
    return true;
  } else {
    uf(NULL, priv);
    wormleaf_unlock_write(leaf);
    return false;
  }
}

  bool
whsafe_inpr(struct wormref * const ref, const struct kref * const key,
    kv_inp_func uf, void * const priv)
{
  wormhole_resume(ref);
  const bool r = wormhole_inpr(ref, key, uf, priv);
  wormhole_park(ref);
  return r;
}

  bool
whsafe_inpw(struct wormref * const ref, const struct kref * const key,
    kv_inp_func uf, void * const priv)
{
  wormhole_resume(ref);
  const bool r = wormhole_inpw(ref, key, uf, priv);
  wormhole_park(ref);
  return r;
}

  bool
whunsafe_inp(struct wormhole * const map, const struct kref * const key,
    kv_inp_func uf, void * const priv)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, key);
  const u32 im = wormleaf_match_hs(leaf, key);
  if (im < WH_KPN) { // overwrite
    uf(wormleaf_kv_at_ih(leaf, im), priv);
    return true;
  } else {
    uf(NULL, priv);
    return false;
  }
}
// }}} put

// del {{{
  static void
wormhole_del_try_merge(struct wormref * const ref, struct wormleaf * const leaf)
{
  struct wormleaf * const next = leaf->next;
  if (next && ((leaf->nr_keys == 0) || ((leaf->nr_keys + next->nr_keys) < WH_KPN_MRG))) {
    // try merge, it may fail if size becomes larger after locking
    wormleaf_lock_write(next, ref);
    (void)wormhole_meta_leaf_merge(ref, leaf);
    // locks are already released; immediately return
  } else {
    wormleaf_unlock_write(leaf);
  }
}

  bool
wormhole_del(struct wormref * const ref, const struct kref * const key)
{
  struct wormleaf * const leaf = wormhole_jump_leaf_write(ref, key);
  const u32 im = wormleaf_match_hs(leaf, key);
  if (im < WH_KPN) { // found
    struct kv * const kv = wormleaf_remove_ih(leaf, im);
    wormhole_del_try_merge(ref, leaf);
    debug_assert(kv);
    // free after releasing locks
    struct wormhole * const map = ref->map;
    map->mm.free(kv, map->mm.priv);
    return true;
  } else {
    wormleaf_unlock_write(leaf);
    return false;
  }
}

  bool
whsafe_del(struct wormref * const ref, const struct kref * const key)
{
  wormhole_resume(ref);
  const bool r = wormhole_del(ref, key);
  wormhole_park(ref);
  return r;
}

  static void
whunsafe_del_try_merge(struct wormhole * const map, struct wormleaf * const leaf)
{
  const u32 n0 = leaf->prev ? leaf->prev->nr_keys : WH_KPN;
  const u32 n1 = leaf->nr_keys;
  const u32 n2 = leaf->next ? leaf->next->nr_keys : WH_KPN;

  if ((leaf->prev && (n1 == 0)) || ((n0 + n1) < WH_KPN_MRG)) {
    whunsafe_meta_leaf_merge(map, leaf->prev, leaf);
  } else if ((leaf->next && (n1 == 0)) || ((n1 + n2) < WH_KPN_MRG)) {
    whunsafe_meta_leaf_merge(map, leaf, leaf->next);
  }
}

  bool
whunsafe_del(struct wormhole * const map, const struct kref * const key)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(map->hmap, key);
  const u32 im = wormleaf_match_hs(leaf, key);
  if (im < WH_KPN) { // found
    struct kv * const kv = wormleaf_remove_ih(leaf, im);
    debug_assert(kv);

    whunsafe_del_try_merge(map, leaf);
    map->mm.free(kv, map->mm.priv);
    return true;
  }
  return false;
}

  u64
wormhole_delr(struct wormref * const ref, const struct kref * const start,
    const struct kref * const end)
{
  struct wormleaf * const leafa = wormhole_jump_leaf_write(ref, start);
  const u32 ia = wormleaf_seek(leafa, start);
  const u32 iaz = end ? wormleaf_seek_end(leafa, end) : leafa->nr_keys;
  if (iaz < ia) { // do nothing if end < start
    wormleaf_unlock_write(leafa);
    return 0;
  }
  u64 ndel = iaz - ia;
  struct wormhole * const map = ref->map;
  wormleaf_delete_range(map, leafa, ia, iaz);
  if (leafa->nr_keys > ia) { // end hit; done
    wormhole_del_try_merge(ref, leafa);
    return ndel;
  }

  while (leafa->next) {
    struct wormleaf * const leafx = leafa->next;
    wormleaf_lock_write(leafx, ref);
    // two leaf nodes locked
    const u32 iz = end ? wormleaf_seek_end(leafx, end) : leafx->nr_keys;
    ndel += iz;
    wormleaf_delete_range(map, leafx, 0, iz);
    if (leafx->nr_keys == 0) { // removed all
      // must hold leaf1's lock for the next iteration
      wormhole_meta_merge(ref, leafa, leafx, false);
    } else { // partially removed; done
      (void)wormhole_meta_leaf_merge(ref, leafa);
      return ndel;
    }
  }
  wormleaf_unlock_write(leafa);
  return ndel;
}

  u64
whsafe_delr(struct wormref * const ref, const struct kref * const start,
    const struct kref * const end)
{
  wormhole_resume(ref);
  const u64 ret = wormhole_delr(ref, start, end);
  wormhole_park(ref);
  return ret;
}

  u64
whunsafe_delr(struct wormhole * const map, const struct kref * const start,
    const struct kref * const end)
{
  // first leaf
  struct wormhmap * const hmap = map->hmap;
  struct wormleaf * const leafa = wormhole_jump_leaf(hmap, start);
  // last leaf
  struct wormleaf * const leafz = end ? wormhole_jump_leaf(hmap, end) : NULL;

  // select start/end on leafa
  const u32 ia = wormleaf_seek(leafa, start);
  const u32 iaz = end ? wormleaf_seek_end(leafa, end) : leafa->nr_keys;
  if (iaz < ia)
    return 0;

  wormleaf_delete_range(map, leafa, ia, iaz);
  u64 ndel = iaz - ia;

  if (leafa == leafz) { // one node only
    whunsafe_del_try_merge(map, leafa);
    return ndel;
  }

  // 0 or more nodes between leafa and leafz
  while (leafa->next != leafz) {
    struct wormleaf * const leafx = leafa->next;
    ndel += leafx->nr_keys;
    for (u32 i = 0; i < leafx->nr_keys; i++)
      map->mm.free(wormleaf_kv_at_is(leafx, i), map->mm.priv);
    leafx->nr_keys = 0;
    whunsafe_meta_leaf_merge(map, leafa, leafx);
  }
  // delete the smaller keys in leafz
  if (leafz) {
    const u32 iz = wormleaf_seek_end(leafz, end);
    wormleaf_delete_range(map, leafz, 0, iz);
    ndel += iz;
    whunsafe_del_try_merge(map, leafa);
  }
  return ndel;
}
// }}} del

// iter {{{
// safe iter: safe sort with read-lock acquired
// unsafe iter: allow concurrent seek/skip
  struct wormhole_iter *
wormhole_iter_create(struct wormref * const ref)
{
  struct wormhole_iter * const iter = malloc(sizeof(*iter));
  if (iter == NULL)
    return NULL;
  iter->ref = ref;
  iter->map = ref->map;
  iter->leaf = NULL;
  iter->is = 0;
  return iter;
}

  static void
wormhole_iter_fix(struct wormhole_iter * const iter)
{
  if (!wormhole_iter_valid(iter))
    return;

  while (unlikely(iter->is >= iter->leaf->nr_keys)) {
    struct wormleaf * const next = iter->leaf->next;
    if (likely(next != NULL)) {
      struct wormref * const ref = iter->ref;
      wormleaf_lock_read(next, ref);
      wormleaf_unlock_read(iter->leaf);

    } else {
      wormleaf_unlock_read(iter->leaf);
    }
    iter->leaf = next;
    iter->is = 0;
    if (!wormhole_iter_valid(iter))
      return;
  }
}

  void
wormhole_iter_seek(struct wormhole_iter * const iter, const struct kref * const key)
{
  debug_assert(key);
  if (iter->leaf)
    wormleaf_unlock_read(iter->leaf);

  struct wormleaf * const leaf = wormhole_jump_leaf_read(iter->ref, key);

  iter->leaf = leaf;
  iter->is = wormleaf_seek(leaf, key);
  wormhole_iter_fix(iter);
}

  void
whsafe_iter_seek(struct wormhole_iter * const iter, const struct kref * const key)
{
  wormhole_resume(iter->ref);
  wormhole_iter_seek(iter, key);
}

  bool
wormhole_iter_valid(struct wormhole_iter * const iter)
{
  return iter->leaf != NULL;
}

  static struct kv *
wormhole_iter_current(struct wormhole_iter * const iter)
{
  if (wormhole_iter_valid(iter)) {
    debug_assert(iter->is < iter->leaf->nr_keys);
    struct kv * const kv = wormleaf_kv_at_is(iter->leaf, iter->is);
    return kv;
  }
  return NULL;
}

  struct kv *
wormhole_iter_peek(struct wormhole_iter * const iter, struct kv * const out)
{
  struct kv * const kv = wormhole_iter_current(iter);
  if (kv) {
    struct kv * const ret = iter->map->mm.out(kv, out);
    return ret;
  }
  return NULL;
}

  bool
wormhole_iter_kref(struct wormhole_iter * const iter, struct kref * const kref)
{
  struct kv * const kv = wormhole_iter_current(iter);
  if (kv) {
    kref_ref_kv(kref, kv);
    return true;
  }
  return false;
}

  bool
wormhole_iter_kvref(struct wormhole_iter * const iter, struct kvref * const kvref)
{
  struct kv * const kv = wormhole_iter_current(iter);
  if (kv) {
    kvref_ref_kv(kvref, kv);
    return true;
  }
  return false;
}

  void
wormhole_iter_skip1(struct wormhole_iter * const iter)
{
  if (wormhole_iter_valid(iter)) {
    iter->is++;
    wormhole_iter_fix(iter);
  }
}

  void
wormhole_iter_skip(struct wormhole_iter * const iter, const u32 nr)
{
  u32 todo = nr;
  while (todo && wormhole_iter_valid(iter)) {
    const u32 cap = iter->leaf->nr_keys - iter->is;
    const u32 nskip = (cap < todo) ? cap : todo;
    iter->is += nskip;
    wormhole_iter_fix(iter);
    todo -= nskip;
  }
}

  struct kv *
wormhole_iter_next(struct wormhole_iter * const iter, struct kv * const out)
{
  struct kv * const ret = wormhole_iter_peek(iter, out);
  wormhole_iter_skip1(iter);
  return ret;
}

  bool
wormhole_iter_inp(struct wormhole_iter * const iter, kv_inp_func uf, void * const priv)
{
  struct kv * const kv = wormhole_iter_current(iter);
  uf(kv, priv); // call uf even if (kv == NULL)
  return kv != NULL;
}

  void
wormhole_iter_park(struct wormhole_iter * const iter)
{
  if (iter->leaf) {
    wormleaf_unlock_read(iter->leaf);
    iter->leaf = NULL;
  }
}

  void
whsafe_iter_park(struct wormhole_iter * const iter)
{
  wormhole_iter_park(iter);
  wormhole_park(iter->ref);
}

  void
wormhole_iter_destroy(struct wormhole_iter * const iter)
{
  if (iter->leaf)
    wormleaf_unlock_read(iter->leaf);
  free(iter);
}

  void
whsafe_iter_destroy(struct wormhole_iter * const iter)
{
  wormhole_park(iter->ref);
  wormhole_iter_destroy(iter);
}
// }}} iter

// unsafe iter {{{
  struct wormhole_iter *
whunsafe_iter_create(struct wormhole * const map)
{
  struct wormhole_iter * const iter = malloc(sizeof(*iter));
  if (iter == NULL)
    return NULL;
  iter->ref = NULL;
  iter->map = map;
  iter->leaf = NULL;
  iter->is = 0;
  whunsafe_iter_seek(iter, kref_null());
  return iter;
}

  static void
whunsafe_iter_fix(struct wormhole_iter * const iter)
{
  if (!wormhole_iter_valid(iter))
    return;

  while (unlikely(iter->is >= iter->leaf->nr_keys)) {
    struct wormleaf * const next = iter->leaf->next;
    iter->leaf = next;
    iter->is = 0;
    if (!wormhole_iter_valid(iter))
      return;
  }
}

  void
whunsafe_iter_seek(struct wormhole_iter * const iter, const struct kref * const key)
{
  struct wormleaf * const leaf = wormhole_jump_leaf(iter->map->hmap, key);

  iter->leaf = leaf;
  iter->is = wormleaf_seek(leaf, key);
  whunsafe_iter_fix(iter);
}

  void
whunsafe_iter_skip1(struct wormhole_iter * const iter)
{
  if (wormhole_iter_valid(iter)) {
    iter->is++;
    whunsafe_iter_fix(iter);
  }
}

  void
whunsafe_iter_skip(struct wormhole_iter * const iter, const u32 nr)
{
  u32 todo = nr;
  while (todo && wormhole_iter_valid(iter)) {
    const u32 cap = iter->leaf->nr_keys - iter->is;
    const u32 nskip = (cap < todo) ? cap : todo;
    iter->is += nskip;
    whunsafe_iter_fix(iter);
    todo -= nskip;
  }
}

  struct kv *
whunsafe_iter_next(struct wormhole_iter * const iter, struct kv * const out)
{
  struct kv * const ret = wormhole_iter_peek(iter, out);
  whunsafe_iter_skip1(iter);
  return ret;
}

  void
whunsafe_iter_destroy(struct wormhole_iter * const iter)
{
  free(iter);
}
// }}} unsafe iter

// misc {{{
  struct wormref *
wormhole_ref(struct wormhole * const map)
{
  struct wormref * const ref = malloc(sizeof(*ref));
  if (ref == NULL)
    return NULL;
  ref->map = map;
  if (qsbr_register(map->qsbr, &(ref->qref)) == false) {
    free(ref);
    return NULL;
  }
  return ref;
}

  struct wormref *
whsafe_ref(struct wormhole * const map)
{
  struct wormref * const ref = wormhole_ref(map);
  if (ref)
    wormhole_park(ref);
  return ref;
}

  struct wormhole *
wormhole_unref(struct wormref * const ref)
{
  struct wormhole * const map = ref->map;
  qsbr_unregister(map->qsbr, &(ref->qref));
  free(ref);
  return map;
}

  inline void
wormhole_park(struct wormref * const ref)
{
  qsbr_park(&(ref->qref));
}

  inline void
wormhole_resume(struct wormref * const ref)
{
  qsbr_resume(&(ref->qref));
}

  inline void
wormhole_refresh_qstate(struct wormref * const ref)
{
  qsbr_update(&(ref->qref), wormhmap_version_load(wormhmap_load(ref->map)));
}

  static void
wormhole_clean_hmap(struct wormhole * const map)
{
  for (u32 x = 0; x < 2; x++) {
    map->hmap2[x].nkeys = 0;
  }
}

  static void
wormhole_free_leaf_keys(struct wormhole * const map, struct wormleaf * const leaf)
{
  const u32 nr = leaf->nr_keys;
  for (u32 i = 0; i < nr; i++) {
    void * const curr = wormleaf_kv_at_is(leaf, i);
    debug_assert(curr);
    map->mm.free(curr, map->mm.priv);
  }
  wormhole_free_akey(leaf->anchor);
}

  static void
wormhole_clean_helper(struct wormhole * const map)
{
  wormhole_clean_hmap(map);
  for (struct wormleaf * leaf = map->leaf0; leaf; leaf = leaf->next)
    wormhole_free_leaf_keys(map, leaf);
  slab_free_all(map->slab_leaf);
  map->leaf0 = NULL;
}

// unsafe
  void
wormhole_clean(struct wormhole * const map)
{
  wormhole_clean_helper(map);
  wormhole_create_leaf0(map);
}

  void
wormhole_destroy(struct wormhole * const map)
{
  wormhole_clean_helper(map);
  for (u32 i = 0; i < 2; i++) {
    struct wormhmap * const hmap = &map->hmap2[i];
    if (hmap->pairs)
      free(hmap->pairs);
  }
  qsbr_destroy(map->qsbr);
  slab_destroy(map->slab_leaf);
  free(map->pbuf);
  free(map);
}

  void
wormhole_fprint(struct wormhole * const map, FILE * const out)
{
  const u64 nr_slab_ul = slab_get_nalloc(map->slab_leaf);
  const u64 nr_slab_um11 = slab_get_nalloc(map->hmap2[0].slab1);
  const u64 nr_slab_um12 = slab_get_nalloc(map->hmap2[0].slab2);
  const u64 nr_slab_um21 = map->hmap2[1].slab1 ? slab_get_nalloc(map->hmap2[1].slab1) : 0;
  const u64 nr_slab_um22 = map->hmap2[1].slab2 ? slab_get_nalloc(map->hmap2[1].slab2) : 0;
  fprintf(out, "%s L-SLAB %lu M-SLAB [0] %lu+%lu [1] %lu+%lu\n",
      __func__, nr_slab_ul, nr_slab_um11, nr_slab_um12, nr_slab_um21, nr_slab_um22);
}
// }}} misc

// api {{{
const struct kvmap_api kvmap_api_wormhole = {
  .hashkey = true,
  .ordered = true,
  .threadsafe = true,
  .unique = true,
  .refpark = true,
  .put = (void *)wormhole_put,
  .get = (void *)wormhole_get,
  .probe = (void *)wormhole_probe,
  .del = (void *)wormhole_del,
  .inpr = (void *)wormhole_inpr,
  .inpw = (void *)wormhole_inpw,
  .merge = (void *)wormhole_merge,
  .delr = (void *)wormhole_delr,
  .iter_create = (void *)wormhole_iter_create,
  .iter_seek = (void *)wormhole_iter_seek,
  .iter_valid = (void *)wormhole_iter_valid,
  .iter_peek = (void *)wormhole_iter_peek,
  .iter_kref = (void *)wormhole_iter_kref,
  .iter_kvref = (void *)wormhole_iter_kvref,
  .iter_skip1 = (void *)wormhole_iter_skip1,
  .iter_skip = (void *)wormhole_iter_skip,
  .iter_next = (void *)wormhole_iter_next,
  .iter_inp = (void *)wormhole_iter_inp,
  .iter_park = (void *)wormhole_iter_park,
  .iter_destroy = (void *)wormhole_iter_destroy,
  .ref = (void *)wormhole_ref,
  .unref = (void *)wormhole_unref,
  .park = (void *)wormhole_park,
  .resume = (void *)wormhole_resume,
  .clean = (void *)wormhole_clean,
  .destroy = (void *)wormhole_destroy,
  .fprint = (void *)wormhole_fprint,
};

const struct kvmap_api kvmap_api_whsafe = {
  .hashkey = true,
  .ordered = true,
  .threadsafe = true,
  .unique = true,
  .put = (void *)whsafe_put,
  .get = (void *)whsafe_get,
  .probe = (void *)whsafe_probe,
  .del = (void *)whsafe_del,
  .inpr = (void *)whsafe_inpr,
  .inpw = (void *)whsafe_inpw,
  .merge = (void *)whsafe_merge,
  .delr = (void *)whsafe_delr,
  .iter_create = (void *)wormhole_iter_create,
  .iter_seek = (void *)whsafe_iter_seek,
  .iter_valid = (void *)wormhole_iter_valid,
  .iter_peek = (void *)wormhole_iter_peek,
  .iter_kref = (void *)wormhole_iter_kref,
  .iter_kvref = (void *)wormhole_iter_kvref,
  .iter_skip1 = (void *)wormhole_iter_skip1,
  .iter_skip = (void *)wormhole_iter_skip,
  .iter_next = (void *)wormhole_iter_next,
  .iter_inp = (void *)wormhole_iter_inp,
  .iter_park = (void *)whsafe_iter_park,
  .iter_destroy = (void *)whsafe_iter_destroy,
  .ref = (void *)whsafe_ref,
  .unref = (void *)wormhole_unref,
  .clean = (void *)wormhole_clean,
  .destroy = (void *)wormhole_destroy,
  .fprint = (void *)wormhole_fprint,
};

const struct kvmap_api kvmap_api_whunsafe = {
  .hashkey = true,
  .ordered = true,
  .unique = true,
  .put = (void *)whunsafe_put,
  .get = (void *)whunsafe_get,
  .probe = (void *)whunsafe_probe,
  .del = (void *)whunsafe_del,
  .inpr = (void *)whunsafe_inp,
  .inpw = (void *)whunsafe_inp,
  .merge = (void *)whunsafe_merge,
  .delr = (void *)whunsafe_delr,
  .iter_create = (void *)whunsafe_iter_create,
  .iter_seek = (void *)whunsafe_iter_seek,
  .iter_valid = (void *)wormhole_iter_valid,
  .iter_peek = (void *)wormhole_iter_peek,
  .iter_kref = (void *)wormhole_iter_kref,
  .iter_kvref = (void *)wormhole_iter_kvref,
  .iter_skip1 = (void *)whunsafe_iter_skip1,
  .iter_skip = (void *)whunsafe_iter_skip,
  .iter_next = (void *)whunsafe_iter_next,
  .iter_inp = (void *)wormhole_iter_inp,
  .iter_destroy = (void *)whunsafe_iter_destroy,
  .clean = (void *)wormhole_clean,
  .destroy = (void *)wormhole_destroy,
  .fprint = (void *)wormhole_fprint,
};

  static void *
wormhole_kvmap_api_create(const char * const name, const struct kvmap_mm * const mm, char ** args)
{
  (void)args;
  if ((!strcmp(name, "wormhole")) || (!strcmp(name, "whsafe"))) {
    return wormhole_create(mm);
  } else if (!strcmp(name, "whunsafe")) {
    return whunsafe_create(mm);
  } else {
    return NULL;
  }
}

__attribute__((constructor))
  static void
wormhole_kvmap_api_init(void)
{
  kvmap_api_register(0, "wormhole", "", wormhole_kvmap_api_create, &kvmap_api_wormhole);
  kvmap_api_register(0, "whsafe", "", wormhole_kvmap_api_create, &kvmap_api_whsafe);
  kvmap_api_register(0, "whunsafe", "", wormhole_kvmap_api_create, &kvmap_api_whunsafe);
}
// }}} api

// vim:fdm=marker
