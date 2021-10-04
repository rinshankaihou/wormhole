/*
 * Copyright (c) 2016--2021  Wu, Xingbo <wuxb45@gmail.com>
 *
 * All rights reserved. No warranty, explicit or implicit, provided.
 */
#pragma once

// C types only; C++ source code don't use this

#include <assert.h>
// #include <stdatomic.h>

/* C11 atomic types */
typedef bool             abool;

typedef char    au8;
typedef short   au16;
typedef int     au32;
typedef long    au64;
static_assert(sizeof(au8) == 1, "sizeof(au8)");
static_assert(sizeof(au16) == 2, "sizeof(au16)");
static_assert(sizeof(au32) == 4, "sizeof(au32)");
static_assert(sizeof(au64) == 8, "sizeof(au64)");

typedef char     as8;
typedef short    as16;
typedef int      as32;
typedef long     as64;
static_assert(sizeof(as8) == 1, "sizeof(as8)");
static_assert(sizeof(as16) == 2, "sizeof(as16)");
static_assert(sizeof(as32) == 4, "sizeof(as32)");
static_assert(sizeof(as64) == 8, "sizeof(as64)");

// shorten long names
#define MO_RELAXED memory_order_relaxed
#define MO_CONSUME memory_order_consume
#define MO_ACQUIRE memory_order_acquire
#define MO_RELEASE memory_order_release
#define MO_ACQ_REL memory_order_acq_rel
#define MO_SEQ_CST memory_order_seq_cst
