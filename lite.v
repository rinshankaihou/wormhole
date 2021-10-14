From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "lite.c".
  Definition normalized := true.
End Info.

Definition __6333 : ident := $"_6333".
Definition __6646 : ident := $"_6646".
Definition __6647 : ident := $"_6647".
Definition __6648 : ident := $"_6648".
Definition __6649 : ident := $"_6649".
Definition __6650 : ident := $"_6650".
Definition __6651 : ident := $"_6651".
Definition __6653 : ident := $"_6653".
Definition __7144 : ident := $"_7144".
Definition __7145 : ident := $"_7145".
Definition __IO_FILE : ident := $"_IO_FILE".
Definition __IO_backup_base : ident := $"_IO_backup_base".
Definition __IO_buf_base : ident := $"_IO_buf_base".
Definition __IO_buf_end : ident := $"_IO_buf_end".
Definition __IO_codecvt : ident := $"_IO_codecvt".
Definition __IO_marker : ident := $"_IO_marker".
Definition __IO_read_base : ident := $"_IO_read_base".
Definition __IO_read_end : ident := $"_IO_read_end".
Definition __IO_read_ptr : ident := $"_IO_read_ptr".
Definition __IO_save_base : ident := $"_IO_save_base".
Definition __IO_save_end : ident := $"_IO_save_end".
Definition __IO_wide_data : ident := $"_IO_wide_data".
Definition __IO_write_base : ident := $"_IO_write_base".
Definition __IO_write_end : ident := $"_IO_write_end".
Definition __IO_write_ptr : ident := $"_IO_write_ptr".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___pad5 : ident := $"__pad5".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition __chain : ident := $"_chain".
Definition __codecvt : ident := $"_codecvt".
Definition __cur_column : ident := $"_cur_column".
Definition __fileno : ident := $"_fileno".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __freeres_buf : ident := $"_freeres_buf".
Definition __freeres_list : ident := $"_freeres_list".
Definition __lock : ident := $"_lock".
Definition __markers : ident := $"_markers".
Definition __mode : ident := $"_mode".
Definition __offset : ident := $"_offset".
Definition __old_offset : ident := $"_old_offset".
Definition __res : ident := $"_res".
Definition __shortbuf : ident := $"_shortbuf".
Definition __unused2 : ident := $"_unused2".
Definition __vtable_offset : ident := $"_vtable_offset".
Definition __wide_data : ident := $"_wide_data".
Definition _anchor : ident := $"anchor".
Definition _anchor2 : ident := $"anchor2".
Definition _async : ident := $"async".
Definition _atomic_load_explicit : ident := $"atomic_load_explicit".
Definition _atomic_store_explicit : ident := $"atomic_store_explicit".
Definition _cap : ident := $"cap".
Definition _clean : ident := $"clean".
Definition _cmp : ident := $"cmp".
Definition _curr : ident := $"curr".
Definition _debug_assert : ident := $"debug_assert".
Definition _del : ident := $"del".
Definition _delr : ident := $"delr".
Definition _destroy : ident := $"destroy".
Definition _fail : ident := $"fail".
Definition _fprint : ident := $"fprint".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _get : ident := $"get".
Definition _hash : ident := $"hash".
Definition _hash32 : ident := $"hash32".
Definition _hashhi : ident := $"hashhi".
Definition _hashkey : ident := $"hashkey".
Definition _hashlo : ident := $"hashlo".
Definition _hdr : ident := $"hdr".
Definition _hmap : ident := $"hmap".
Definition _hmap0 : ident := $"hmap0".
Definition _hmap1 : ident := $"hmap1".
Definition _hmap2 : ident := $"hmap2".
Definition _hmap__1 : ident := $"hmap__1".
Definition _hmap_ptr : ident := $"hmap_ptr".
Definition _hv : ident := $"hv".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _im : ident := $"im".
Definition _in : ident := $"in".
Definition _inpr : ident := $"inpr".
Definition _inpw : ident := $"inpw".
Definition _irefsafe : ident := $"irefsafe".
Definition _is : ident := $"is".
Definition _iter : ident := $"iter".
Definition _iter_create : ident := $"iter_create".
Definition _iter_destroy : ident := $"iter_destroy".
Definition _iter_inp : ident := $"iter_inp".
Definition _iter_kref : ident := $"iter_kref".
Definition _iter_kvref : ident := $"iter_kvref".
Definition _iter_next : ident := $"iter_next".
Definition _iter_park : ident := $"iter_park".
Definition _iter_peek : ident := $"iter_peek".
Definition _iter_release : ident := $"iter_release".
Definition _iter_retain : ident := $"iter_retain".
Definition _iter_seek : ident := $"iter_seek".
Definition _iter_skip : ident := $"iter_skip".
Definition _iter_skip1 : ident := $"iter_skip1".
Definition _iter_valid : ident := $"iter_valid".
Definition _key : ident := $"key".
Definition _klen : ident := $"klen".
Definition _kptr : ident := $"kptr".
Definition _kref : ident := $"kref".
Definition _kref__1 : ident := $"kref__1".
Definition _kref_kv_compare : ident := $"kref_kv_compare".
Definition _kref_ref_kv : ident := $"kref_ref_kv".
Definition _kv : ident := $"kv".
Definition _kv__1 : ident := $"kv__1".
Definition _kv_compare : ident := $"kv_compare".
Definition _kv_dup2 : ident := $"kv_dup2".
Definition _kv_dup_key : ident := $"kv_dup_key".
Definition _kv_kref : ident := $"kv_kref".
Definition _kv_null : ident := $"kv_null".
Definition _kvlen : ident := $"kvlen".
Definition _kvmap_api : ident := $"kvmap_api".
Definition _kvmap_api_litemap : ident := $"kvmap_api_litemap".
Definition _kvmap_mm : ident := $"kvmap_mm".
Definition _kvmap_mm_dup : ident := $"kvmap_mm_dup".
Definition _kvref : ident := $"kvref".
Definition _kvref__1 : ident := $"kvref__1".
Definition _kvref_ref_kv : ident := $"kvref_ref_kv".
Definition _kvs : ident := $"kvs".
Definition _l : ident := $"l".
Definition _leaf : ident := $"leaf".
Definition _leaf0 : ident := $"leaf0".
Definition _leaf1 : ident := $"leaf1".
Definition _leaf2 : ident := $"leaf2".
Definition _leaflock : ident := $"leaflock".
Definition _len : ident := $"len".
Definition _litehmap : ident := $"litehmap".
Definition _litehmap_jump_i : ident := $"litehmap_jump_i".
Definition _litehmap_load : ident := $"litehmap_load".
Definition _litehmap_lock : ident := $"litehmap_lock".
Definition _litehmap_seek_ge : ident := $"litehmap_seek_ge".
Definition _litehmap_store : ident := $"litehmap_store".
Definition _litehmap_switch : ident := $"litehmap_switch".
Definition _litehmap_unlock : ident := $"litehmap_unlock".
Definition _litehmap_version_load : ident := $"litehmap_version_load".
Definition _litehmap_version_store : ident := $"litehmap_version_store".
Definition _liteleaf : ident := $"liteleaf".
Definition _liteleaf_alloc : ident := $"liteleaf_alloc".
Definition _liteleaf_free : ident := $"liteleaf_free".
Definition _liteleaf_insert : ident := $"liteleaf_insert".
Definition _liteleaf_lock_read : ident := $"liteleaf_lock_read".
Definition _liteleaf_lock_write : ident := $"liteleaf_lock_write".
Definition _liteleaf_match_i : ident := $"liteleaf_match_i".
Definition _liteleaf_merge : ident := $"liteleaf_merge".
Definition _liteleaf_remove : ident := $"liteleaf_remove".
Definition _liteleaf_seek_ge : ident := $"liteleaf_seek_ge".
Definition _liteleaf_split_undo : ident := $"liteleaf_split_undo".
Definition _liteleaf_unlock_read : ident := $"liteleaf_unlock_read".
Definition _liteleaf_unlock_write : ident := $"liteleaf_unlock_write".
Definition _liteleaf_update : ident := $"liteleaf_update".
Definition _liteleaf_version_load : ident := $"liteleaf_version_load".
Definition _liteleaf_version_store : ident := $"liteleaf_version_store".
Definition _litemap : ident := $"litemap".
Definition _litemap_clean : ident := $"litemap_clean".
Definition _litemap_clean_helper : ident := $"litemap_clean_helper".
Definition _litemap_clean_hmap : ident := $"litemap_clean_hmap".
Definition _litemap_create : ident := $"litemap_create".
Definition _litemap_create_leaf0 : ident := $"litemap_create_leaf0".
Definition _litemap_del : ident := $"litemap_del".
Definition _litemap_del_try_merge : ident := $"litemap_del_try_merge".
Definition _litemap_destroy : ident := $"litemap_destroy".
Definition _litemap_fprint : ident := $"litemap_fprint".
Definition _litemap_free_leaf_keys : ident := $"litemap_free_leaf_keys".
Definition _litemap_get : ident := $"litemap_get".
Definition _litemap_iter : ident := $"litemap_iter".
Definition _litemap_iter_create : ident := $"litemap_iter_create".
Definition _litemap_iter_current : ident := $"litemap_iter_current".
Definition _litemap_iter_destroy : ident := $"litemap_iter_destroy".
Definition _litemap_iter_fix : ident := $"litemap_iter_fix".
Definition _litemap_iter_inp : ident := $"litemap_iter_inp".
Definition _litemap_iter_kref : ident := $"litemap_iter_kref".
Definition _litemap_iter_kvref : ident := $"litemap_iter_kvref".
Definition _litemap_iter_next : ident := $"litemap_iter_next".
Definition _litemap_iter_park : ident := $"litemap_iter_park".
Definition _litemap_iter_peek : ident := $"litemap_iter_peek".
Definition _litemap_iter_seek : ident := $"litemap_iter_seek".
Definition _litemap_iter_skip : ident := $"litemap_iter_skip".
Definition _litemap_iter_skip1 : ident := $"litemap_iter_skip1".
Definition _litemap_iter_valid : ident := $"litemap_iter_valid".
Definition _litemap_jump_leaf : ident := $"litemap_jump_leaf".
Definition _litemap_jump_leaf_read : ident := $"litemap_jump_leaf_read".
Definition _litemap_jump_leaf_write : ident := $"litemap_jump_leaf_write".
Definition _litemap_meta_leaf_merge : ident := $"litemap_meta_leaf_merge".
Definition _litemap_meta_merge : ident := $"litemap_meta_merge".
Definition _litemap_park : ident := $"litemap_park".
Definition _litemap_probe : ident := $"litemap_probe".
Definition _litemap_put : ident := $"litemap_put".
Definition _litemap_qsbr_update_pause : ident := $"litemap_qsbr_update_pause".
Definition _litemap_ref : ident := $"litemap_ref".
Definition _litemap_refresh_qstate : ident := $"litemap_refresh_qstate".
Definition _litemap_resume : ident := $"litemap_resume".
Definition _litemap_split_insert : ident := $"litemap_split_insert".
Definition _litemap_split_leaf : ident := $"litemap_split_leaf".
Definition _litemap_split_meta : ident := $"litemap_split_meta".
Definition _litemap_unref : ident := $"litemap_unref".
Definition _litemeta_merge : ident := $"litemeta_merge".
Definition _litemeta_split : ident := $"litemeta_split".
Definition _literef : ident := $"literef".
Definition _lv : ident := $"lv".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _map : ident := $"map".
Definition _memmove : ident := $"memmove".
Definition _memset : ident := $"memset".
Definition _merge : ident := $"merge".
Definition _metalock : ident := $"metalock".
Definition _mm : ident := $"mm".
Definition _n1 : ident := $"n1".
Definition _nalloc : ident := $"nalloc".
Definition _new : ident := $"new".
Definition _next : ident := $"next".
Definition _nkeys : ident := $"nkeys".
Definition _nr : ident := $"nr".
Definition _nr_keys : ident := $"nr_keys".
Definition _nskip : ident := $"nskip".
Definition _old : ident := $"old".
Definition _opaque : ident := $"opaque".
Definition _ordered : ident := $"ordered".
Definition _out : ident := $"out".
Definition _padding : ident := $"padding".
Definition _padding0 : ident := $"padding0".
Definition _padding1 : ident := $"padding1".
Definition _padding2 : ident := $"padding2".
Definition _pairs : ident := $"pairs".
Definition _pairs1 : ident := $"pairs1".
Definition _park : ident := $"park".
Definition _prev : ident := $"prev".
Definition _priv : ident := $"priv".
Definition _privhi : ident := $"privhi".
Definition _privlo : ident := $"privlo".
Definition _privptr : ident := $"privptr".
Definition _probe : ident := $"probe".
Definition _ptr : ident := $"ptr".
Definition _put : ident := $"put".
Definition _qref : ident := $"qref".
Definition _qsbr : ident := $"qsbr".
Definition _qsbr_create : ident := $"qsbr_create".
Definition _qsbr_destroy : ident := $"qsbr_destroy".
Definition _qsbr_park : ident := $"qsbr_park".
Definition _qsbr_ref : ident := $"qsbr_ref".
Definition _qsbr_register : ident := $"qsbr_register".
Definition _qsbr_resume : ident := $"qsbr_resume".
Definition _qsbr_unregister : ident := $"qsbr_unregister".
Definition _qsbr_update : ident := $"qsbr_update".
Definition _qsbr_wait : ident := $"qsbr_wait".
Definition _r : ident := $"r".
Definition _readonly : ident := $"readonly".
Definition _realloc : ident := $"realloc".
Definition _ref : ident := $"ref".
Definition _refcnt : ident := $"refcnt".
Definition _refpark : ident := $"refpark".
Definition _reserved : ident := $"reserved".
Definition _resume : ident := $"resume".
Definition _ret : ident := $"ret".
Definition _rsi : ident := $"rsi".
Definition _rsm : ident := $"rsm".
Definition _rwlock_init : ident := $"rwlock_init".
Definition _rwlock_lock_read : ident := $"rwlock_lock_read".
Definition _rwlock_lock_write : ident := $"rwlock_lock_write".
Definition _rwlock_trylock_read : ident := $"rwlock_trylock_read".
Definition _rwlock_trylock_read_nr : ident := $"rwlock_trylock_read_nr".
Definition _rwlock_trylock_write : ident := $"rwlock_trylock_write".
Definition _rwlock_trylock_write_nr : ident := $"rwlock_trylock_write_nr".
Definition _rwlock_unlock_read : ident := $"rwlock_unlock_read".
Definition _rwlock_unlock_write : ident := $"rwlock_unlock_write".
Definition _slab : ident := $"slab".
Definition _slab__1 : ident := $"slab__1".
Definition _slab_alloc_safe : ident := $"slab_alloc_safe".
Definition _slab_create : ident := $"slab_create".
Definition _slab_destroy : ident := $"slab_destroy".
Definition _slab_free_all : ident := $"slab_free_all".
Definition _slab_free_safe : ident := $"slab_free_safe".
Definition _slab_leaf : ident := $"slab_leaf".
Definition _sync : ident := $"sync".
Definition _threadsafe : ident := $"threadsafe".
Definition _tmp : ident := $"tmp".
Definition _todo : ident := $"todo".
Definition _uf : ident := $"uf".
Definition _unique : ident := $"unique".
Definition _unlock_leaf1 : ident := $"unlock_leaf1".
Definition _unref : ident := $"unref".
Definition _v : ident := $"v".
Definition _v1 : ident := $"v1".
Definition _vlen : ident := $"vlen".
Definition _vptr : ident := $"vptr".
Definition _x : ident := $"x".
Definition _yalloc : ident := $"yalloc".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_kvmap_mm_dup := {|
  gvar_info := (Tstruct _kvmap_mm noattr);
  gvar_init := nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_liteleaf_alloc := {|
  fn_return := (tptr (Tstruct _liteleaf noattr));
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_prev, (tptr (Tstruct _liteleaf noattr))) ::
                (_next, (tptr (Tstruct _liteleaf noattr))) ::
                (_anchor, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _slab noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
            (Tstruct _litemap noattr)) _slab_leaf
          (tptr (Tstruct _slab noattr))))
      (Scall (Some _t'1)
        (Evar _slab_alloc_safe (Tfunction
                                 (Tcons (tptr (Tstruct _slab noattr)) Tnil)
                                 (tptr tvoid) cc_default))
        ((Etempvar _t'2 (tptr (Tstruct _slab noattr))) :: nil)))
    (Sset _leaf (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _rwlock_init (Tfunction
                             (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid
                             cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
               (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
           (tptr (Tunion __6333 noattr))) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _prev
            (tptr (Tstruct _liteleaf noattr)))
          (Etempvar _prev (tptr (Tstruct _liteleaf noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                (Tstruct _liteleaf noattr)) _next
              (tptr (Tstruct _liteleaf noattr)))
            (Etempvar _next (tptr (Tstruct _liteleaf noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _anchor
                (tptr (Tstruct _kv noattr)))
              (Etempvar _anchor (tptr (Tstruct _kv noattr))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _nr_keys tuint)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))))))))))))
|}.

Definition f_liteleaf_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_slab__1, (tptr (Tstruct _slab noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
        _opaque tuint))
    (Scall None
      (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
      ((Ebinop Oeq (Etempvar _t'2 tuint) (Econst_int (Int.repr 0) tint) tint) ::
       nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _anchor (tptr (Tstruct _kv noattr))))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _kv noattr))) :: nil)))
    (Scall None
      (Evar _slab_free_safe (Tfunction
                              (Tcons (tptr (Tstruct _slab noattr))
                                (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
      ((Etempvar _slab__1 (tptr (Tstruct _slab noattr))) ::
       (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))))
|}.

Definition f_liteleaf_lock_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
                (_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _rwlock_trylock_write (Tfunction
                                  (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                                  tbool cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
           (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
       (tptr (Tunion __6333 noattr))) :: nil))
  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
    (Ssequence
      (Scall None
        (Evar _litemap_park (Tfunction
                              (Tcons (tptr (Tstruct _literef noattr)) Tnil)
                              tvoid cc_default))
        ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
      (Ssequence
        (Scall None
          (Evar _rwlock_lock_write (Tfunction
                                     (Tcons (tptr (Tunion __6333 noattr))
                                       Tnil) tvoid cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                 (Tstruct _liteleaf noattr)) _leaflock
               (Tunion __6333 noattr)) (tptr (Tunion __6333 noattr))) :: nil))
        (Scall None
          (Evar _litemap_resume (Tfunction
                                  (Tcons (tptr (Tstruct _literef noattr))
                                    Tnil) tvoid cc_default))
          ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))))
    Sskip))
|}.

Definition f_liteleaf_lock_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
                (_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _rwlock_trylock_read (Tfunction
                                 (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                                 tbool cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
           (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
       (tptr (Tunion __6333 noattr))) :: nil))
  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
    (Ssequence
      (Scall None
        (Evar _litemap_park (Tfunction
                              (Tcons (tptr (Tstruct _literef noattr)) Tnil)
                              tvoid cc_default))
        ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
      (Ssequence
        (Scall None
          (Evar _rwlock_lock_read (Tfunction
                                    (Tcons (tptr (Tunion __6333 noattr))
                                      Tnil) tvoid cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                 (Tstruct _liteleaf noattr)) _leaflock
               (Tunion __6333 noattr)) (tptr (Tunion __6333 noattr))) :: nil))
        (Scall None
          (Evar _litemap_resume (Tfunction
                                  (Tcons (tptr (Tstruct _literef noattr))
                                    Tnil) tvoid cc_default))
          ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))))
    Sskip))
|}.

Definition f_liteleaf_unlock_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _rwlock_unlock_write (Tfunction
                               (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                               tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
         (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
     (tptr (Tunion __6333 noattr))) :: nil))
|}.

Definition f_liteleaf_unlock_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _rwlock_unlock_read (Tfunction
                              (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                              tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
         (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
     (tptr (Tunion __6333 noattr))) :: nil))
|}.

Definition f_litehmap_lock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _rwlock_trylock_write (Tfunction
                                  (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                                  tbool cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
           (Tstruct _litemap noattr)) _metalock (Tunion __6333 noattr))
       (tptr (Tunion __6333 noattr))) :: nil))
  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
    (Ssequence
      (Scall None
        (Evar _litemap_park (Tfunction
                              (Tcons (tptr (Tstruct _literef noattr)) Tnil)
                              tvoid cc_default))
        ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
      (Ssequence
        (Scall None
          (Evar _rwlock_lock_write (Tfunction
                                     (Tcons (tptr (Tunion __6333 noattr))
                                       Tnil) tvoid cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                 (Tstruct _litemap noattr)) _metalock (Tunion __6333 noattr))
             (tptr (Tunion __6333 noattr))) :: nil))
        (Scall None
          (Evar _litemap_resume (Tfunction
                                  (Tcons (tptr (Tstruct _literef noattr))
                                    Tnil) tvoid cc_default))
          ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))))
    Sskip))
|}.

Definition f_litehmap_unlock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _rwlock_unlock_write (Tfunction
                               (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                               tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
         (Tstruct _litemap noattr)) _metalock (Tunion __6333 noattr))
     (tptr (Tunion __6333 noattr))) :: nil))
|}.

Definition f_litehmap_switch := {|
  fn_return := (tptr (Tstruct _litehmap noattr));
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_hmap, (tptr (Tstruct _litehmap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _litehmap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                 (Efield
                   (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                     (Tstruct _litemap noattr)) _hmap2
                   (tarray (Tstruct _litehmap noattr) 2)) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Oadd (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Econst_int (Int.repr 1) tint) (tptr (Tstruct _litehmap noattr)))
        (tptr (Tstruct _litehmap noattr))))
    (Sset _t'1
      (Ecast
        (Ebinop Osub (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Econst_int (Int.repr 1) tint) (tptr (Tstruct _litehmap noattr)))
        (tptr (Tstruct _litehmap noattr)))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _litehmap noattr))))))
|}.

Definition f_litehmap_load := {|
  fn_return := (tptr (Tstruct _litehmap noattr));
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _atomic_load_explicit (Tfunction Tnil tint
                                  {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
    ((Eaddrof
       (Efield
         (Efield
           (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
             (Tstruct _litemap noattr)) 18727075383868559167%positive
           (Tunion __7145 noattr)) _hmap_ptr (tvolatile tlong))
       (tptr (tvolatile tlong))) :: (Econst_int (Int.repr 2) tint) :: nil))
  (Sreturn (Some (Ecast (Etempvar _t'1 tint)
                   (tptr (Tstruct _litehmap noattr))))))
|}.

Definition f_litehmap_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_hmap, (tptr (Tstruct _litehmap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _atomic_store_explicit (Tfunction Tnil tint
                                 {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
  ((Eaddrof
     (Efield
       (Efield
         (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
           (Tstruct _litemap noattr)) 18727075383868559167%positive
         (Tunion __7145 noattr)) _hmap_ptr (tvolatile tlong))
     (tptr (tvolatile tlong))) ::
   (Ecast (Etempvar _hmap (tptr (Tstruct _litehmap noattr))) tulong) ::
   (Econst_int (Int.repr 3) tint) :: nil))
|}.

Definition f_litehmap_version_load := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _atomic_load_explicit (Tfunction Tnil tint
                                  {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
           (Tstruct _litehmap noattr)) _hv tlong) (tptr tlong)) ::
     (Econst_int (Int.repr 2) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_litehmap_version_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) :: (_v, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _atomic_store_explicit (Tfunction Tnil tint
                                 {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
         (Tstruct _litehmap noattr)) _hv tlong) (tptr tlong)) ::
   (Etempvar _v tulong) :: (Econst_int (Int.repr 3) tint) :: nil))
|}.

Definition f_liteleaf_version_load := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _atomic_load_explicit (Tfunction Tnil tint
                                  {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
           (Tstruct _liteleaf noattr)) _lv tlong) (tptr tlong)) ::
     (Econst_int (Int.repr 1) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_liteleaf_version_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_v, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _atomic_store_explicit (Tfunction Tnil tint
                                 {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
         (Tstruct _liteleaf noattr)) _lv tlong) (tptr tlong)) ::
   (Etempvar _v tulong) :: (Econst_int (Int.repr 3) tint) :: nil))
|}.

Definition f_litemap_qsbr_update_pause := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: (_v, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _qsbr_update (Tfunction
                       (Tcons (tptr (Tstruct _qsbr_ref noattr))
                         (Tcons tulong Tnil)) tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
         (Tstruct _literef noattr)) _qref (Tstruct _qsbr_ref noattr))
     (tptr (Tstruct _qsbr_ref noattr))) :: (Etempvar _v tulong) :: nil))
|}.

Definition f_litemap_create_leaf0 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_anchor, (tptr (Tstruct _kv noattr))) ::
               (_leaf0, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'3, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'2, (tptr (Tstruct _kv noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _kv noattr) tulong) :: nil))
    (Sset _anchor (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _anchor (tptr (Tstruct _kv noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _kv_null (Tfunction Tnil (tptr (Tstruct _kv noattr))
                           cc_default)) nil)
        (Scall None
          (Evar _kv_dup2 (Tfunction
                           (Tcons (tptr (Tstruct _kv noattr))
                             (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                           (tptr (Tstruct _kv noattr)) cc_default))
          ((Etempvar _t'2 (tptr (Tstruct _kv noattr))) ::
           (Etempvar _anchor (tptr (Tstruct _kv noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _liteleaf_alloc (Tfunction
                                    (Tcons (tptr (Tstruct _litemap noattr))
                                      (Tcons
                                        (tptr (Tstruct _liteleaf noattr))
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          (Tcons (tptr (Tstruct _kv noattr))
                                            Tnil))))
                                    (tptr (Tstruct _liteleaf noattr))
                                    cc_default))
            ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Etempvar _anchor (tptr (Tstruct _kv noattr))) :: nil))
          (Sset _leaf0 (Etempvar _t'3 (tptr (Tstruct _liteleaf noattr)))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _leaf0 (tptr (Tstruct _liteleaf noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _anchor (tptr (Tstruct _kv noattr))) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))
            Sskip)
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _leaf0
                (tptr (Tstruct _liteleaf noattr)))
              (Etempvar _leaf0 (tptr (Tstruct _liteleaf noattr))))
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))
|}.

Definition f_litemap_create := {|
  fn_return := (tptr (Tstruct _litemap noattr));
  fn_callconv := cc_default;
  fn_params := ((_mm, (tptr (Tstruct _kvmap_mm noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_leaf0, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
               (_hmap, (tptr (Tstruct _litehmap noattr))) ::
               (_i__1, tuint) ::
               (_hmap__1, (tptr (Tstruct _litehmap noattr))) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tbool) ::
               (_t'4, (tptr (Tstruct _qsbr noattr))) ::
               (_t'3, (tptr (Tstruct _slab noattr))) ::
               (_t'2, (Tstruct _kvmap_mm noattr)) :: (_t'1, (tptr tvoid)) ::
               (_t'21, (tptr (Tstruct _slab noattr))) ::
               (_t'20, (tptr (Tstruct _qsbr noattr))) ::
               (_t'19, (tptr (Tstruct __7144 noattr))) ::
               (_t'18, (tptr (Tstruct __7144 noattr))) ::
               (_t'17, (tptr (Tstruct _kv noattr))) ::
               (_t'16, (tptr (Tstruct __7144 noattr))) ::
               (_t'15, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'14, (tptr (Tstruct _slab noattr))) ::
               (_t'13, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'12, (tptr (Tstruct _qsbr noattr))) ::
               (_t'11, (tptr (Tstruct _qsbr noattr))) ::
               (_t'10, (tptr (Tstruct _slab noattr))) ::
               (_t'9, (tptr (Tstruct _slab noattr))) ::
               (_t'8, (tptr (Tstruct __7144 noattr))) ::
               (_t'7, (tptr (Tstruct __7144 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _yalloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _litemap noattr) tulong) :: nil))
    (Sset _map (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _map (tptr (Tstruct _litemap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction
                        (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
                        (tptr tvoid) cc_default))
        ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
         (Econst_int (Int.repr 0) tint) ::
         (Esizeof (Tstruct _litemap noattr) tulong) :: nil))
      (Ssequence
        (Ssequence
          (Sifthenelse (Etempvar _mm (tptr (Tstruct _kvmap_mm noattr)))
            (Sset _t'2
              (Ecast
                (Ederef (Etempvar _mm (tptr (Tstruct _kvmap_mm noattr)))
                  (Tstruct _kvmap_mm noattr)) (Tstruct _kvmap_mm noattr)))
            (Sset _t'2
              (Ecast (Evar _kvmap_mm_dup (Tstruct _kvmap_mm noattr))
                (Tstruct _kvmap_mm noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                (Tstruct _litemap noattr)) _mm (Tstruct _kvmap_mm noattr))
            (Etempvar _t'2 (Tstruct _kvmap_mm noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _slab_create (Tfunction
                                   (Tcons tulong (Tcons tulong Tnil))
                                   (tptr (Tstruct _slab noattr)) cc_default))
              ((Esizeof (Tstruct _liteleaf noattr) tulong) ::
               (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
                 (Econst_int (Int.repr 21) tint) tulong) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _slab_leaf
                (tptr (Tstruct _slab noattr)))
              (Etempvar _t'3 (tptr (Tstruct _slab noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'21
                (Efield
                  (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                    (Tstruct _litemap noattr)) _slab_leaf
                  (tptr (Tstruct _slab noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'21 (tptr (Tstruct _slab noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sgoto _fail)
                Sskip))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _qsbr_create (Tfunction Tnil
                                       (tptr (Tstruct _qsbr noattr))
                                       cc_default)) nil)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                      (Tstruct _litemap noattr)) _qsbr
                    (tptr (Tstruct _qsbr noattr)))
                  (Etempvar _t'4 (tptr (Tstruct _qsbr noattr)))))
              (Ssequence
                (Ssequence
                  (Sset _t'20
                    (Efield
                      (Ederef
                        (Etempvar _map (tptr (Tstruct _litemap noattr)))
                        (Tstruct _litemap noattr)) _qsbr
                      (tptr (Tstruct _qsbr noattr))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _t'20 (tptr (Tstruct _qsbr noattr)))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Sgoto _fail)
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _litemap_create_leaf0 (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _litemap noattr))
                                                      Tnil) tbool cc_default))
                      ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                       nil))
                    (Sifthenelse (Eunop Onotbool (Etempvar _t'5 tbool) tint)
                      (Sgoto _fail)
                      Sskip))
                  (Ssequence
                    (Sset _leaf0
                      (Efield
                        (Ederef
                          (Etempvar _map (tptr (Tstruct _litemap noattr)))
                          (Tstruct _litemap noattr)) _leaf0
                        (tptr (Tstruct _liteleaf noattr))))
                    (Ssequence
                      (Ssequence
                        (Sset _i (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                           (Econst_int (Int.repr 2) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _hmap
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                      (Tstruct _litemap noattr)) _hmap2
                                    (tarray (Tstruct _litehmap noattr) 2))
                                  (Etempvar _i tuint)
                                  (tptr (Tstruct _litehmap noattr))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                      (Tstruct _litehmap noattr)) _nalloc
                                    tulong) (Econst_int (Int.repr 256) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'6)
                                      (Evar _malloc (Tfunction
                                                      (Tcons tulong Tnil)
                                                      (tptr tvoid)
                                                      cc_default))
                                      ((Ebinop Omul
                                         (Esizeof (Tstruct __7144 noattr) tulong)
                                         (Econst_int (Int.repr 256) tint)
                                         tulong) :: nil))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                          (Tstruct _litehmap noattr)) _pairs
                                        (tptr (Tstruct __7144 noattr)))
                                      (Etempvar _t'6 (tptr tvoid))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'19
                                        (Efield
                                          (Ederef
                                            (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                            (Tstruct _litehmap noattr))
                                          _pairs
                                          (tptr (Tstruct __7144 noattr))))
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _t'19 (tptr (Tstruct __7144 noattr)))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        (Sgoto _fail)
                                        Sskip))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'18
                                          (Efield
                                            (Ederef
                                              (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                              (Tstruct _litehmap noattr))
                                            _pairs
                                            (tptr (Tstruct __7144 noattr))))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'18 (tptr (Tstruct __7144 noattr)))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (Tstruct __7144 noattr)))
                                              (Tstruct __7144 noattr)) _leaf
                                            (tptr (Tstruct _liteleaf noattr)))
                                          (Etempvar _leaf0 (tptr (Tstruct _liteleaf noattr)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'16
                                            (Efield
                                              (Ederef
                                                (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                                (Tstruct _litehmap noattr))
                                              _pairs
                                              (tptr (Tstruct __7144 noattr))))
                                          (Ssequence
                                            (Sset _t'17
                                              (Efield
                                                (Ederef
                                                  (Etempvar _leaf0 (tptr (Tstruct _liteleaf noattr)))
                                                  (Tstruct _liteleaf noattr))
                                                _anchor
                                                (tptr (Tstruct _kv noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'16 (tptr (Tstruct __7144 noattr)))
                                                    (Econst_int (Int.repr 0) tint)
                                                    (tptr (Tstruct __7144 noattr)))
                                                  (Tstruct __7144 noattr))
                                                _anchor
                                                (tptr (Tstruct _kv noattr)))
                                              (Etempvar _t'17 (tptr (Tstruct _kv noattr))))))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                              (Tstruct _litehmap noattr))
                                            _nkeys tulong)
                                          (Econst_int (Int.repr 1) tint)))))))))
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      (Ssequence
                        (Scall None
                          (Evar _rwlock_init (Tfunction
                                               (Tcons
                                                 (tptr (Tunion __6333 noattr))
                                                 Tnil) tvoid cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                 (Tstruct _litemap noattr)) _metalock
                               (Tunion __6333 noattr))
                             (tptr (Tunion __6333 noattr))) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _litehmap_store (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _litemap noattr))
                                                      (Tcons
                                                        (tptr (Tstruct _litehmap noattr))
                                                        Tnil)) tvoid
                                                    cc_default))
                            ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                             (Ebinop Oadd
                               (Efield
                                 (Ederef
                                   (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                   (Tstruct _litemap noattr)) _hmap2
                                 (tarray (Tstruct _litehmap noattr) 2))
                               (Econst_int (Int.repr 0) tint)
                               (tptr (Tstruct _litehmap noattr))) :: nil))
                          (Ssequence
                            (Sreturn (Some (Etempvar _map (tptr (Tstruct _litemap noattr)))))
                            (Ssequence
                              (Slabel _fail
                                (Ssequence
                                  (Sset _t'13
                                    (Efield
                                      (Ederef
                                        (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                        (Tstruct _litemap noattr)) _leaf0
                                      (tptr (Tstruct _liteleaf noattr))))
                                  (Sifthenelse (Etempvar _t'13 (tptr (Tstruct _liteleaf noattr)))
                                    (Ssequence
                                      (Sset _t'14
                                        (Efield
                                          (Ederef
                                            (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                            (Tstruct _litemap noattr))
                                          _slab_leaf
                                          (tptr (Tstruct _slab noattr))))
                                      (Ssequence
                                        (Sset _t'15
                                          (Efield
                                            (Ederef
                                              (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                              (Tstruct _litemap noattr))
                                            _leaf0
                                            (tptr (Tstruct _liteleaf noattr))))
                                        (Scall None
                                          (Evar _liteleaf_free (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _slab noattr))
                                                                   (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                          ((Etempvar _t'14 (tptr (Tstruct _slab noattr))) ::
                                           (Etempvar _t'15 (tptr (Tstruct _liteleaf noattr))) ::
                                           nil))))
                                    Sskip)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                        (Tstruct _litemap noattr)) _qsbr
                                      (tptr (Tstruct _qsbr noattr))))
                                  (Sifthenelse (Etempvar _t'11 (tptr (Tstruct _qsbr noattr)))
                                    (Ssequence
                                      (Sset _t'12
                                        (Efield
                                          (Ederef
                                            (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                            (Tstruct _litemap noattr)) _qsbr
                                          (tptr (Tstruct _qsbr noattr))))
                                      (Scall None
                                        (Evar _qsbr_destroy (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _qsbr noattr))
                                                                Tnil) tvoid
                                                              cc_default))
                                        ((Etempvar _t'12 (tptr (Tstruct _qsbr noattr))) ::
                                         nil)))
                                    Sskip))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Efield
                                        (Ederef
                                          (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                          (Tstruct _litemap noattr))
                                        _slab_leaf
                                        (tptr (Tstruct _slab noattr))))
                                    (Sifthenelse (Etempvar _t'9 (tptr (Tstruct _slab noattr)))
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                              (Tstruct _litemap noattr))
                                            _slab_leaf
                                            (tptr (Tstruct _slab noattr))))
                                        (Scall None
                                          (Evar _slab_destroy (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _slab noattr))
                                                                  Tnil) tvoid
                                                                cc_default))
                                          ((Etempvar _t'10 (tptr (Tstruct _slab noattr))) ::
                                           nil)))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i__1
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i__1 tuint)
                                                         (Econst_int (Int.repr 2) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sset _hmap__1
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                                    (Tstruct _litemap noattr))
                                                  _hmap2
                                                  (tarray (Tstruct _litehmap noattr) 2))
                                                (Etempvar _i__1 tuint)
                                                (tptr (Tstruct _litehmap noattr))))
                                            (Ssequence
                                              (Sset _t'7
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _hmap__1 (tptr (Tstruct _litehmap noattr)))
                                                    (Tstruct _litehmap noattr))
                                                  _pairs
                                                  (tptr (Tstruct __7144 noattr))))
                                              (Sifthenelse (Etempvar _t'7 (tptr (Tstruct __7144 noattr)))
                                                (Ssequence
                                                  (Sset _t'8
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _hmap__1 (tptr (Tstruct _litehmap noattr)))
                                                        (Tstruct _litehmap noattr))
                                                      _pairs
                                                      (tptr (Tstruct __7144 noattr))))
                                                  (Scall None
                                                    (Evar _free (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Etempvar _t'8 (tptr (Tstruct __7144 noattr))) ::
                                                     nil)))
                                                Sskip))))
                                        (Sset _i__1
                                          (Ebinop Oadd (Etempvar _i__1 tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _free (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                        ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                                         nil))
                                      (Sreturn (Some (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)))))))))))))))))))))))
|}.

Definition f_litehmap_jump_i := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tulong) :: (_r, tulong) :: (_m, tulong) ::
               (_cmp, tint) :: (_t'1, tint) ::
               (_t'3, (tptr (Tstruct _kv noattr))) ::
               (_t'2, (tptr (Tstruct __7144 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _r
      (Efield
        (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Tstruct _litehmap noattr)) _nkeys tulong))
    (Ssequence
      (Swhile
        (Ebinop Olt
          (Ebinop Oadd (Etempvar _l tulong) (Econst_int (Int.repr 1) tint)
            tulong) (Etempvar _r tulong) tint)
        (Ssequence
          (Sset _m
            (Ebinop Oshr
              (Ebinop Oadd (Etempvar _l tulong) (Etempvar _r tulong) tulong)
              (Econst_int (Int.repr 1) tint) tulong))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                      (Tstruct _litehmap noattr)) _pairs
                    (tptr (Tstruct __7144 noattr))))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'2 (tptr (Tstruct __7144 noattr)))
                          (Etempvar _m tulong)
                          (tptr (Tstruct __7144 noattr)))
                        (Tstruct __7144 noattr)) _anchor
                      (tptr (Tstruct _kv noattr))))
                  (Scall (Some _t'1)
                    (Evar _kref_kv_compare (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _kref noattr))
                                               (Tcons
                                                 (tptr (Tstruct _kv noattr))
                                                 Tnil)) tint cc_default))
                    ((Etempvar _key (tptr (Tstruct _kref noattr))) ::
                     (Etempvar _t'3 (tptr (Tstruct _kv noattr))) :: nil))))
              (Sset _cmp (Etempvar _t'1 tint)))
            (Sifthenelse (Ebinop Olt (Etempvar _cmp tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _r (Etempvar _m tulong))
              (Sifthenelse (Ebinop Ogt (Etempvar _cmp tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _l (Etempvar _m tulong))
                (Sreturn (Some (Etempvar _m tulong))))))))
      (Sreturn (Some (Etempvar _l tulong))))))
|}.

Definition f_litemap_jump_leaf := {|
  fn_return := (tptr (Tstruct _liteleaf noattr));
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tulong) ::
               (_t'3, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'2, (tptr (Tstruct __7144 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litehmap_jump_i (Tfunction
                               (Tcons (tptr (Tstruct _litehmap noattr))
                                 (Tcons (tptr (Tstruct _kref noattr)) Tnil))
                               tulong cc_default))
      ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) ::
       (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
    (Sset _i (Etempvar _t'1 tulong)))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Tstruct _litehmap noattr)) _pairs (tptr (Tstruct __7144 noattr))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct __7144 noattr)))
              (Etempvar _i tulong) (tptr (Tstruct __7144 noattr)))
            (Tstruct __7144 noattr)) _leaf (tptr (Tstruct _liteleaf noattr))))
      (Sreturn (Some (Etempvar _t'3 (tptr (Tstruct _liteleaf noattr))))))))
|}.

Definition f_litemap_jump_leaf_read := {|
  fn_return := (tptr (Tstruct _liteleaf noattr));
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_hmap, (tptr (Tstruct _litehmap noattr))) :: (_v, tulong) ::
               (_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_v1, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, (tptr (Tstruct _litehmap noattr))) :: (_t'5, tbool) ::
               (_t'4, tulong) :: (_t'3, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'2, tulong) :: (_t'1, (tptr (Tstruct _litehmap noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _map
    (Efield
      (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
        (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
  (Sloop
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _litehmap_load (Tfunction
                                 (Tcons (tptr (Tstruct _litemap noattr))
                                   Tnil) (tptr (Tstruct _litehmap noattr))
                                 cc_default))
          ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
        (Sset _hmap (Etempvar _t'1 (tptr (Tstruct _litehmap noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _litehmap_version_load (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _litehmap noattr))
                                             Tnil) tulong cc_default))
            ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) :: nil))
          (Sset _v (Etempvar _t'2 tulong)))
        (Ssequence
          (Scall None
            (Evar _qsbr_update (Tfunction
                                 (Tcons (tptr (Tstruct _qsbr_ref noattr))
                                   (Tcons tulong Tnil)) tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                   (Tstruct _literef noattr)) _qref
                 (Tstruct _qsbr_ref noattr))
               (tptr (Tstruct _qsbr_ref noattr))) :: (Etempvar _v tulong) ::
             nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _litemap_jump_leaf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _litehmap noattr))
                                             (Tcons
                                               (tptr (Tstruct _kref noattr))
                                               Tnil))
                                           (tptr (Tstruct _liteleaf noattr))
                                           cc_default))
                ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) ::
                 (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
              (Sset _leaf (Etempvar _t'3 (tptr (Tstruct _liteleaf noattr)))))
            (Sloop
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _rwlock_trylock_read_nr (Tfunction
                                                    (Tcons
                                                      (tptr (Tunion __6333 noattr))
                                                      (Tcons tushort Tnil))
                                                    tbool cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                           (Tstruct _liteleaf noattr)) _leaflock
                         (Tunion __6333 noattr))
                       (tptr (Tunion __6333 noattr))) ::
                     (Econst_int (Int.repr 64) tint) :: nil))
                  (Sifthenelse (Etempvar _t'5 tbool)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _liteleaf_version_load (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _liteleaf noattr))
                                                           Tnil) tulong
                                                         cc_default))
                          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                           nil))
                        (Sifthenelse (Ebinop Ole (Etempvar _t'4 tulong)
                                       (Etempvar _v tulong) tint)
                          (Sreturn (Some (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))))
                          Sskip))
                      (Ssequence
                        (Scall None
                          (Evar _liteleaf_unlock_read (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _liteleaf noattr))
                                                          Tnil) tvoid
                                                        cc_default))
                          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                           nil))
                        Sbreak))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _litehmap_load (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _litemap noattr))
                                                 Tnil)
                                               (tptr (Tstruct _litehmap noattr))
                                               cc_default))
                        ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                         nil))
                      (Scall (Some _t'7)
                        (Evar _litehmap_version_load (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _litehmap noattr))
                                                         Tnil) tulong
                                                       cc_default))
                        ((Etempvar _t'6 (tptr (Tstruct _litehmap noattr))) ::
                         nil)))
                    (Sset _v1 (Etempvar _t'7 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _liteleaf_version_load (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _liteleaf noattr))
                                                         Tnil) tulong
                                                       cc_default))
                        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                         nil))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'8 tulong)
                                     (Etempvar _v tulong) tint)
                        Sbreak
                        Sskip))
                    (Scall None
                      (Evar _litemap_qsbr_update_pause (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _literef noattr))
                                                           (Tcons tulong
                                                             Tnil)) tvoid
                                                         cc_default))
                      ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
                       (Etempvar _v1 tulong) :: nil)))))
              Sskip)))))
    Sskip))
|}.

Definition f_litemap_jump_leaf_write := {|
  fn_return := (tptr (Tstruct _liteleaf noattr));
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_hmap, (tptr (Tstruct _litehmap noattr))) :: (_v, tulong) ::
               (_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_v1, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, (tptr (Tstruct _litehmap noattr))) :: (_t'5, tbool) ::
               (_t'4, tulong) :: (_t'3, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'2, tulong) :: (_t'1, (tptr (Tstruct _litehmap noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _map
    (Efield
      (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
        (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
  (Sloop
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _litehmap_load (Tfunction
                                 (Tcons (tptr (Tstruct _litemap noattr))
                                   Tnil) (tptr (Tstruct _litehmap noattr))
                                 cc_default))
          ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
        (Sset _hmap (Etempvar _t'1 (tptr (Tstruct _litehmap noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _litehmap_version_load (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _litehmap noattr))
                                             Tnil) tulong cc_default))
            ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) :: nil))
          (Sset _v (Etempvar _t'2 tulong)))
        (Ssequence
          (Scall None
            (Evar _qsbr_update (Tfunction
                                 (Tcons (tptr (Tstruct _qsbr_ref noattr))
                                   (Tcons tulong Tnil)) tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                   (Tstruct _literef noattr)) _qref
                 (Tstruct _qsbr_ref noattr))
               (tptr (Tstruct _qsbr_ref noattr))) :: (Etempvar _v tulong) ::
             nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _litemap_jump_leaf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _litehmap noattr))
                                             (Tcons
                                               (tptr (Tstruct _kref noattr))
                                               Tnil))
                                           (tptr (Tstruct _liteleaf noattr))
                                           cc_default))
                ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) ::
                 (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
              (Sset _leaf (Etempvar _t'3 (tptr (Tstruct _liteleaf noattr)))))
            (Sloop
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _rwlock_trylock_write_nr (Tfunction
                                                     (Tcons
                                                       (tptr (Tunion __6333 noattr))
                                                       (Tcons tushort Tnil))
                                                     tbool cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                           (Tstruct _liteleaf noattr)) _leaflock
                         (Tunion __6333 noattr))
                       (tptr (Tunion __6333 noattr))) ::
                     (Econst_int (Int.repr 64) tint) :: nil))
                  (Sifthenelse (Etempvar _t'5 tbool)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _liteleaf_version_load (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _liteleaf noattr))
                                                           Tnil) tulong
                                                         cc_default))
                          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                           nil))
                        (Sifthenelse (Ebinop Ole (Etempvar _t'4 tulong)
                                       (Etempvar _v tulong) tint)
                          (Sreturn (Some (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))))
                          Sskip))
                      (Ssequence
                        (Scall None
                          (Evar _liteleaf_unlock_write (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _liteleaf noattr))
                                                           Tnil) tvoid
                                                         cc_default))
                          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                           nil))
                        Sbreak))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _litehmap_load (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _litemap noattr))
                                                 Tnil)
                                               (tptr (Tstruct _litehmap noattr))
                                               cc_default))
                        ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                         nil))
                      (Scall (Some _t'7)
                        (Evar _litehmap_version_load (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _litehmap noattr))
                                                         Tnil) tulong
                                                       cc_default))
                        ((Etempvar _t'6 (tptr (Tstruct _litehmap noattr))) ::
                         nil)))
                    (Sset _v1 (Etempvar _t'7 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _liteleaf_version_load (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _liteleaf noattr))
                                                         Tnil) tulong
                                                       cc_default))
                        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                         nil))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'8 tulong)
                                     (Etempvar _v tulong) tint)
                        Sbreak
                        Sskip))
                    (Scall None
                      (Evar _litemap_qsbr_update_pause (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _literef noattr))
                                                           (Tcons tulong
                                                             Tnil)) tvoid
                                                         cc_default))
                      ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
                       (Etempvar _v1 tulong) :: nil)))))
              Sskip)))))
    Sskip))
|}.

Definition f_liteleaf_match_i := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tuint) :: (_r, tuint) :: (_m, tuint) :: (_cmp, tint) ::
               (_t'1, tint) :: (_t'2, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _r
      (Efield
        (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _nr_keys tuint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _l tuint) (Etempvar _r tuint) tint)
        (Ssequence
          (Sset _m
            (Ebinop Oshr
              (Ebinop Oadd (Etempvar _l tuint) (Etempvar _r tuint) tuint)
              (Econst_int (Int.repr 1) tint) tuint))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                          (Tstruct _liteleaf noattr)) _kvs
                        (tarray (tptr (Tstruct _kv noattr)) 128))
                      (Etempvar _m tuint) (tptr (tptr (Tstruct _kv noattr))))
                    (tptr (Tstruct _kv noattr))))
                (Scall (Some _t'1)
                  (Evar _kref_kv_compare (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _kref noattr))
                                             (Tcons
                                               (tptr (Tstruct _kv noattr))
                                               Tnil)) tint cc_default))
                  ((Etempvar _key (tptr (Tstruct _kref noattr))) ::
                   (Etempvar _t'2 (tptr (Tstruct _kv noattr))) :: nil)))
              (Sset _cmp (Etempvar _t'1 tint)))
            (Sifthenelse (Ebinop Olt (Etempvar _cmp tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _r (Etempvar _m tuint))
              (Sifthenelse (Ebinop Ogt (Etempvar _cmp tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _l
                  (Ebinop Oadd (Etempvar _m tuint)
                    (Econst_int (Int.repr 1) tint) tuint))
                (Sreturn (Some (Etempvar _m tuint))))))))
      (Sreturn (Some (Econst_int (Int.repr 128) tuint))))))
|}.

Definition f_liteleaf_seek_ge := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tuint) :: (_r, tuint) :: (_m, tuint) :: (_cmp, tint) ::
               (_t'1, tint) :: (_t'2, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _r
      (Efield
        (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _nr_keys tuint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _l tuint) (Etempvar _r tuint) tint)
        (Ssequence
          (Sset _m
            (Ebinop Oshr
              (Ebinop Oadd (Etempvar _l tuint) (Etempvar _r tuint) tuint)
              (Econst_int (Int.repr 1) tint) tuint))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                          (Tstruct _liteleaf noattr)) _kvs
                        (tarray (tptr (Tstruct _kv noattr)) 128))
                      (Etempvar _m tuint) (tptr (tptr (Tstruct _kv noattr))))
                    (tptr (Tstruct _kv noattr))))
                (Scall (Some _t'1)
                  (Evar _kref_kv_compare (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _kref noattr))
                                             (Tcons
                                               (tptr (Tstruct _kv noattr))
                                               Tnil)) tint cc_default))
                  ((Etempvar _key (tptr (Tstruct _kref noattr))) ::
                   (Etempvar _t'2 (tptr (Tstruct _kv noattr))) :: nil)))
              (Sset _cmp (Etempvar _t'1 tint)))
            (Sifthenelse (Ebinop Olt (Etempvar _cmp tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _r (Etempvar _m tuint))
              (Sifthenelse (Ebinop Ogt (Etempvar _cmp tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _l
                  (Ebinop Oadd (Etempvar _m tuint)
                    (Econst_int (Int.repr 1) tint) tuint))
                (Sreturn (Some (Ebinop Oor (Etempvar _m tuint)
                                 (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                   (Econst_int (Int.repr 31) tint) tuint)
                                 tuint))))))))
      (Sreturn (Some (Etempvar _l tuint))))))
|}.

Definition f_liteleaf_update := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                (_new, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_old, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _old
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _kvs
          (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
        (tptr (tptr (Tstruct _kv noattr)))) (tptr (Tstruct _kv noattr))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _kvs
            (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
          (tptr (tptr (Tstruct _kv noattr)))) (tptr (Tstruct _kv noattr)))
      (Etempvar _new (tptr (Tstruct _kv noattr))))
    (Sreturn (Some (Etempvar _old (tptr (Tstruct _kv noattr)))))))
|}.

Definition f_liteleaf_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                (_new, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _nr_keys tuint))
    (Scall None
      (Evar _memmove (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                       (tptr tvoid) cc_default))
      ((Ebinop Oadd
         (Efield
           (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
             (Tstruct _liteleaf noattr)) _kvs
           (tarray (tptr (Tstruct _kv noattr)) 128))
         (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
           tuint) (tptr (tptr (Tstruct _kv noattr)))) ::
       (Ebinop Oadd
         (Efield
           (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
             (Tstruct _liteleaf noattr)) _kvs
           (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
         (tptr (tptr (Tstruct _kv noattr)))) ::
       (Ebinop Omul (Esizeof (tptr (Tstruct _kv noattr)) tulong)
         (Ebinop Osub (Etempvar _t'2 tuint) (Etempvar _i tuint) tuint)
         tulong) :: nil)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _kvs
            (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
          (tptr (tptr (Tstruct _kv noattr)))) (tptr (Tstruct _kv noattr)))
      (Etempvar _new (tptr (Tstruct _kv noattr))))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint)
        (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_litemap_split_leaf := {|
  fn_return := (tptr (Tstruct _liteleaf noattr));
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_leaf1, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                (_new, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_anchor2, (tptr (Tstruct _kv noattr))) ::
               (_leaf2, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'2, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _kv noattr))) ::
               (_t'3, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _nr_keys tuint))
    (Scall None
      (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
      ((Ebinop Oeq (Etempvar _t'5 tuint) (Econst_int (Int.repr 128) tuint)
         tint) :: nil)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _kvs
                (tarray (tptr (Tstruct _kv noattr)) 128))
              (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                (Econst_int (Int.repr 1) tint) tuint)
              (tptr (tptr (Tstruct _kv noattr))))
            (tptr (Tstruct _kv noattr))))
        (Scall (Some _t'1)
          (Evar _kv_dup_key (Tfunction
                              (Tcons (tptr (Tstruct _kv noattr)) Tnil)
                              (tptr (Tstruct _kv noattr)) cc_default))
          ((Etempvar _t'4 (tptr (Tstruct _kv noattr))) :: nil)))
      (Sset _anchor2 (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _anchor2 (tptr (Tstruct _kv noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _next
                (tptr (Tstruct _liteleaf noattr))))
            (Scall (Some _t'2)
              (Evar _liteleaf_alloc (Tfunction
                                      (Tcons (tptr (Tstruct _litemap noattr))
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          (Tcons
                                            (tptr (Tstruct _liteleaf noattr))
                                            (Tcons
                                              (tptr (Tstruct _kv noattr))
                                              Tnil))))
                                      (tptr (Tstruct _liteleaf noattr))
                                      cc_default))
              ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
               (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
               (Etempvar _t'3 (tptr (Tstruct _liteleaf noattr))) ::
               (Etempvar _anchor2 (tptr (Tstruct _kv noattr))) :: nil)))
          (Sset _leaf2 (Etempvar _t'2 (tptr (Tstruct _liteleaf noattr)))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _anchor2 (tptr (Tstruct _kv noattr))) :: nil))
              (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)))))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _memmove (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                               (tptr tvoid) cc_default))
              ((Ebinop Oadd
                 (Efield
                   (Ederef
                     (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                     (Tstruct _liteleaf noattr)) _kvs
                   (tarray (tptr (Tstruct _kv noattr)) 128))
                 (Econst_int (Int.repr 0) tint)
                 (tptr (tptr (Tstruct _kv noattr)))) ::
               (Ebinop Oadd
                 (Efield
                   (Ederef
                     (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                     (Tstruct _liteleaf noattr)) _kvs
                   (tarray (tptr (Tstruct _kv noattr)) 128))
                 (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                   (Econst_int (Int.repr 1) tint) tuint)
                 (tptr (tptr (Tstruct _kv noattr)))) ::
               (Ebinop Omul (Esizeof (tptr (Tstruct _kv noattr)) tulong)
                 (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                   (Econst_int (Int.repr 1) tint) tuint) tulong) :: nil))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _nr_keys tuint)
                (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                  (Econst_int (Int.repr 1) tint) tuint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                      (Tstruct _liteleaf noattr)) _nr_keys tuint)
                  (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                    (Econst_int (Int.repr 1) tint) tuint))
                (Ssequence
                  (Sifthenelse (Ebinop Ole (Etempvar _i tuint)
                                 (Ebinop Oshr
                                   (Econst_int (Int.repr 128) tuint)
                                   (Econst_int (Int.repr 1) tint) tuint)
                                 tint)
                    (Scall None
                      (Evar _liteleaf_insert (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _liteleaf noattr))
                                                 (Tcons tuint
                                                   (Tcons
                                                     (tptr (Tstruct _kv noattr))
                                                     Tnil))) tvoid
                                               cc_default))
                      ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                       (Etempvar _i tuint) ::
                       (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil))
                    (Scall None
                      (Evar _liteleaf_insert (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _liteleaf noattr))
                                                 (Tcons tuint
                                                   (Tcons
                                                     (tptr (Tstruct _kv noattr))
                                                     Tnil))) tvoid
                                               cc_default))
                      ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                       (Ebinop Osub (Etempvar _i tuint)
                         (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                           (Econst_int (Int.repr 1) tint) tuint) tuint) ::
                       (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil)))
                  (Sreturn (Some (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))))))))))))))
|}.

Definition f_liteleaf_remove := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _kv__1
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _kvs
          (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
        (tptr (tptr (Tstruct _kv noattr)))) (tptr (Tstruct _kv noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint))
      (Scall None
        (Evar _memmove (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                         (tptr tvoid) cc_default))
        ((Ebinop Oadd
           (Efield
             (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
               (Tstruct _liteleaf noattr)) _kvs
             (tarray (tptr (Tstruct _kv noattr)) 128)) (Etempvar _i tuint)
           (tptr (tptr (Tstruct _kv noattr)))) ::
         (Ebinop Oadd
           (Efield
             (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
               (Tstruct _liteleaf noattr)) _kvs
             (tarray (tptr (Tstruct _kv noattr)) 128))
           (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
             tuint) (tptr (tptr (Tstruct _kv noattr)))) ::
         (Ebinop Omul (Esizeof (tptr (Tstruct _kv noattr)) tulong)
           (Ebinop Osub
             (Ebinop Osub (Etempvar _t'2 tuint) (Etempvar _i tuint) tuint)
             (Econst_int (Int.repr 1) tint) tuint) tulong) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint)
          (Ebinop Osub (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      (Sreturn (Some (Etempvar _kv__1 (tptr (Tstruct _kv noattr))))))))
|}.

Definition f_liteleaf_merge := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_leaf1, (tptr (Tstruct _liteleaf noattr))) ::
                (_leaf2, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _nr_keys tuint))
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint))
      (Scall None
        (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
        ((Ebinop Olt
           (Ebinop Oadd (Etempvar _t'5 tuint) (Etempvar _t'6 tuint) tuint)
           (Econst_int (Int.repr 128) tuint) tint) :: nil))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Scall None
          (Evar _memmove (Tfunction
                           (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                           (tptr tvoid) cc_default))
          ((Ebinop Oadd
             (Efield
               (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                 (Tstruct _liteleaf noattr)) _kvs
               (tarray (tptr (Tstruct _kv noattr)) 128))
             (Etempvar _t'3 tuint) (tptr (tptr (Tstruct _kv noattr)))) ::
           (Ebinop Oadd
             (Efield
               (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                 (Tstruct _liteleaf noattr)) _kvs
               (tarray (tptr (Tstruct _kv noattr)) 128))
             (Econst_int (Int.repr 0) tint)
             (tptr (tptr (Tstruct _kv noattr)))) ::
           (Ebinop Omul (Esizeof (tptr (Tstruct _kv noattr)) tulong)
             (Etempvar _t'4 tuint) tulong) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                (Tstruct _liteleaf noattr)) _nr_keys tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                (Tstruct _liteleaf noattr)) _nr_keys tuint)
            (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint) tuint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint)
          (Econst_int (Int.repr 0) tint))
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_liteleaf_split_undo := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_leaf1, (tptr (Tstruct _liteleaf noattr))) ::
                (_leaf2, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _slab noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _i tuint)
                 (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                   (Econst_int (Int.repr 1) tint) tuint) tint)
    (Scall None
      (Evar _liteleaf_remove (Tfunction
                               (Tcons (tptr (Tstruct _liteleaf noattr))
                                 (Tcons tuint Tnil))
                               (tptr (Tstruct _kv noattr)) cc_default))
      ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
       (Etempvar _i tuint) :: nil))
    (Scall None
      (Evar _liteleaf_remove (Tfunction
                               (Tcons (tptr (Tstruct _liteleaf noattr))
                                 (Tcons tuint Tnil))
                               (tptr (Tstruct _kv noattr)) cc_default))
      ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
       (Ebinop Osub (Etempvar _i tuint)
         (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
           (Econst_int (Int.repr 1) tint) tuint) tuint) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _nr_keys tuint))
      (Scall None
        (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
        ((Ebinop Oeq (Etempvar _t'3 tuint)
           (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
             (Econst_int (Int.repr 1) tint) tuint) tint) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Scall None
          (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
          ((Ebinop Oeq (Etempvar _t'2 tuint)
             (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
               (Econst_int (Int.repr 1) tint) tuint) tint) :: nil)))
      (Ssequence
        (Scall None
          (Evar _liteleaf_merge (Tfunction
                                  (Tcons (tptr (Tstruct _liteleaf noattr))
                                    (Tcons (tptr (Tstruct _liteleaf noattr))
                                      Tnil)) tbool cc_default))
          ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
           (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _liteleaf_unlock_write (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _liteleaf noattr))
                                             Tnil) tvoid cc_default))
            ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) :: nil))
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _slab_leaf
                (tptr (Tstruct _slab noattr))))
            (Scall None
              (Evar _liteleaf_free (Tfunction
                                     (Tcons (tptr (Tstruct _slab noattr))
                                       (Tcons
                                         (tptr (Tstruct _liteleaf noattr))
                                         Tnil)) tvoid cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _slab noattr))) ::
               (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) :: nil))))))))
|}.

Definition f_litemap_get := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) ::
                (_out, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
               (_tmp, (tptr (Tstruct _kv noattr))) ::
               (_t'4, (tptr (Tstruct _kv noattr))) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tuint) :: (_t'1, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'7, (tptr (Tstruct _kv noattr))) ::
               (_t'6,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                        (tptr (Tstruct _kv noattr)) cc_default))) ::
               (_t'5, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_jump_leaf_read (Tfunction
                                      (Tcons (tptr (Tstruct _literef noattr))
                                        (Tcons (tptr (Tstruct _kref noattr))
                                          Tnil))
                                      (tptr (Tstruct _liteleaf noattr))
                                      cc_default))
      ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
       (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
    (Sset _leaf (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _liteleaf_match_i (Tfunction
                                  (Tcons (tptr (Tstruct _liteleaf noattr))
                                    (Tcons (tptr (Tstruct _kref noattr))
                                      Tnil)) tuint cc_default))
        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
         (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
      (Sset _i (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 128) tuint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                    (Tstruct _literef noattr)) _map
                  (tptr (Tstruct _litemap noattr))))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _t'5 (tptr (Tstruct _litemap noattr)))
                        (Tstruct _litemap noattr)) _mm
                      (Tstruct _kvmap_mm noattr)) _out
                    (tptr (Tfunction
                            (Tcons (tptr (Tstruct _kv noattr))
                              (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                            (tptr (Tstruct _kv noattr)) cc_default))))
                (Ssequence
                  (Sset _t'7
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                            (Tstruct _liteleaf noattr)) _kvs
                          (tarray (tptr (Tstruct _kv noattr)) 128))
                        (Etempvar _i tuint)
                        (tptr (tptr (Tstruct _kv noattr))))
                      (tptr (Tstruct _kv noattr))))
                  (Scall (Some _t'4)
                    (Etempvar _t'6 (tptr (Tfunction
                                           (Tcons (tptr (Tstruct _kv noattr))
                                             (Tcons
                                               (tptr (Tstruct _kv noattr))
                                               Tnil))
                                           (tptr (Tstruct _kv noattr))
                                           cc_default)))
                    ((Etempvar _t'7 (tptr (Tstruct _kv noattr))) ::
                     (Etempvar _out (tptr (Tstruct _kv noattr))) :: nil)))))
            (Sset _t'3
              (Ecast (Etempvar _t'4 (tptr (Tstruct _kv noattr)))
                (tptr tvoid))))
          (Sset _t'3
            (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
              (tptr tvoid))))
        (Sset _tmp (Etempvar _t'3 (tptr tvoid))))
      (Ssequence
        (Scall None
          (Evar _liteleaf_unlock_read (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          Tnil) tvoid cc_default))
          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Sreturn (Some (Etempvar _tmp (tptr (Tstruct _kv noattr)))))))))
|}.

Definition f_litemap_probe := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
               (_r, tbool) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_jump_leaf_read (Tfunction
                                      (Tcons (tptr (Tstruct _literef noattr))
                                        (Tcons (tptr (Tstruct _kref noattr))
                                          Tnil))
                                      (tptr (Tstruct _liteleaf noattr))
                                      cc_default))
      ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
       (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
    (Sset _leaf (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _liteleaf_match_i (Tfunction
                                  (Tcons (tptr (Tstruct _liteleaf noattr))
                                    (Tcons (tptr (Tstruct _kref noattr))
                                      Tnil)) tuint cc_default))
        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
         (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
      (Sset _i (Etempvar _t'2 tuint)))
    (Ssequence
      (Sset _r
        (Ecast
          (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 128) tuint)
            tint) tbool))
      (Ssequence
        (Scall None
          (Evar _liteleaf_unlock_read (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          Tnil) tvoid cc_default))
          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Sreturn (Some (Etempvar _r tbool)))))))
|}.

Definition f_litehmap_seek_ge := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) ::
                (_anchor, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tulong) :: (_r, tulong) :: (_m, tulong) ::
               (_cmp, tint) :: (_t'1, tint) ::
               (_t'3, (tptr (Tstruct _kv noattr))) ::
               (_t'2, (tptr (Tstruct __7144 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _r
      (Efield
        (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Tstruct _litehmap noattr)) _nkeys tulong))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _l tulong) (Etempvar _r tulong) tint)
        (Ssequence
          (Sset _m
            (Ebinop Oshr
              (Ebinop Oadd (Etempvar _l tulong) (Etempvar _r tulong) tulong)
              (Econst_int (Int.repr 1) tint) tulong))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                      (Tstruct _litehmap noattr)) _pairs
                    (tptr (Tstruct __7144 noattr))))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'2 (tptr (Tstruct __7144 noattr)))
                          (Etempvar _m tulong)
                          (tptr (Tstruct __7144 noattr)))
                        (Tstruct __7144 noattr)) _anchor
                      (tptr (Tstruct _kv noattr))))
                  (Scall (Some _t'1)
                    (Evar _kv_compare (Tfunction
                                        (Tcons (tptr (Tstruct _kv noattr))
                                          (Tcons (tptr (Tstruct _kv noattr))
                                            Tnil)) tint cc_default))
                    ((Etempvar _anchor (tptr (Tstruct _kv noattr))) ::
                     (Etempvar _t'3 (tptr (Tstruct _kv noattr))) :: nil))))
              (Sset _cmp (Etempvar _t'1 tint)))
            (Sifthenelse (Ebinop Olt (Etempvar _cmp tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _r (Etempvar _m tulong))
              (Sifthenelse (Ebinop Ogt (Etempvar _cmp tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _l
                  (Ebinop Oadd (Etempvar _m tulong)
                    (Econst_int (Int.repr 1) tint) tulong))
                (Sreturn (Some (Etempvar _m tulong))))))))
      (Sreturn (Some (Etempvar _l tulong))))))
|}.

Definition f_litemeta_split := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_n1, tulong) :: (_pairs1, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tulong) :: (_t'16, tulong) ::
               (_t'15, tulong) :: (_t'14, (tptr (Tstruct _kv noattr))) ::
               (_t'13, tulong) :: (_t'12, (tptr (Tstruct __7144 noattr))) ::
               (_t'11, (tptr (Tstruct __7144 noattr))) ::
               (_t'10, (tptr (Tstruct __7144 noattr))) ::
               (_t'9, (tptr (Tstruct _kv noattr))) ::
               (_t'8, (tptr (Tstruct __7144 noattr))) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, (tptr (Tstruct __7144 noattr))) ::
               (_t'4, tulong) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'15
      (Efield
        (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
          (Tstruct _litehmap noattr)) _nalloc tulong))
    (Ssequence
      (Sset _t'16
        (Efield
          (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
            (Tstruct _litehmap noattr)) _nkeys tulong))
      (Scall None
        (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
        ((Ebinop Ogt (Etempvar _t'15 tulong) (Etempvar _t'16 tulong) tint) ::
         nil))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'14
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _anchor
            (tptr (Tstruct _kv noattr))))
        (Scall (Some _t'1)
          (Evar _litehmap_seek_ge (Tfunction
                                    (Tcons (tptr (Tstruct _litehmap noattr))
                                      (Tcons (tptr (Tstruct _kv noattr))
                                        Tnil)) tulong cc_default))
          ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) ::
           (Etempvar _t'14 (tptr (Tstruct _kv noattr))) :: nil)))
      (Sset _i (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
              (Tstruct _litehmap noattr)) _pairs
            (tptr (Tstruct __7144 noattr))))
        (Ssequence
          (Sset _t'12
            (Efield
              (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                (Tstruct _litehmap noattr)) _pairs
              (tptr (Tstruct __7144 noattr))))
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                  (Tstruct _litehmap noattr)) _nkeys tulong))
            (Scall None
              (Evar _memmove (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                               (tptr tvoid) cc_default))
              ((Ebinop Oadd (Etempvar _t'11 (tptr (Tstruct __7144 noattr)))
                 (Ebinop Oadd (Etempvar _i tulong)
                   (Econst_int (Int.repr 1) tint) tulong)
                 (tptr (Tstruct __7144 noattr))) ::
               (Ebinop Oadd (Etempvar _t'12 (tptr (Tstruct __7144 noattr)))
                 (Etempvar _i tulong) (tptr (Tstruct __7144 noattr))) ::
               (Ebinop Omul (Esizeof (Tstruct __7144 noattr) tulong)
                 (Ebinop Osub (Etempvar _t'13 tulong) (Etempvar _i tulong)
                   tulong) tulong) :: nil)))))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                (Tstruct _litehmap noattr)) _pairs
              (tptr (Tstruct __7144 noattr))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd (Etempvar _t'10 (tptr (Tstruct __7144 noattr)))
                  (Etempvar _i tulong) (tptr (Tstruct __7144 noattr)))
                (Tstruct __7144 noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr)))
            (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                  (Tstruct _litehmap noattr)) _pairs
                (tptr (Tstruct __7144 noattr))))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _anchor
                  (tptr (Tstruct _kv noattr))))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _t'8 (tptr (Tstruct __7144 noattr)))
                      (Etempvar _i tulong) (tptr (Tstruct __7144 noattr)))
                    (Tstruct __7144 noattr)) _anchor
                  (tptr (Tstruct _kv noattr)))
                (Etempvar _t'9 (tptr (Tstruct _kv noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                    (Tstruct _litehmap noattr)) _nkeys tulong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                    (Tstruct _litehmap noattr)) _nkeys tulong)
                (Ebinop Oadd (Etempvar _t'7 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                    (Tstruct _litehmap noattr)) _nkeys tulong))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                      (Tstruct _litehmap noattr)) _nalloc tulong))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tulong)
                               (Etempvar _t'4 tulong) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                            (Tstruct _litehmap noattr)) _nalloc tulong))
                      (Sset _n1
                        (Ebinop Oadd (Etempvar _t'6 tulong)
                          (Econst_int (Int.repr 256) tint) tulong)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'5
                            (Efield
                              (Ederef
                                (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                (Tstruct _litehmap noattr)) _pairs
                              (tptr (Tstruct __7144 noattr))))
                          (Scall (Some _t'2)
                            (Evar _realloc (Tfunction
                                             (Tcons (tptr tvoid)
                                               (Tcons tulong Tnil))
                                             (tptr tvoid) cc_default))
                            ((Etempvar _t'5 (tptr (Tstruct __7144 noattr))) ::
                             (Ebinop Omul
                               (Esizeof (Tstruct __7144 noattr) tulong)
                               (Etempvar _n1 tulong) tulong) :: nil)))
                        (Sset _pairs1 (Etempvar _t'2 (tptr tvoid))))
                      (Sifthenelse (Etempvar _pairs1 (tptr tvoid))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                (Tstruct _litehmap noattr)) _nalloc tulong)
                            (Etempvar _n1 tulong))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                                (Tstruct _litehmap noattr)) _pairs
                              (tptr (Tstruct __7144 noattr)))
                            (Etempvar _pairs1 (tptr tvoid))))
                        Sskip)))
                  Sskip)))))))))
|}.

Definition f_litemap_split_meta := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_leaf2, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_hmap0, (tptr (Tstruct _litehmap noattr))) ::
               (_hmap1, (tptr (Tstruct _litehmap noattr))) ::
               (_leaf1, (tptr (Tstruct _liteleaf noattr))) ::
               (_v1, tulong) :: (_t'4, tulong) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _litehmap noattr))) ::
               (_t'1, (tptr (Tstruct _litehmap noattr))) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'6, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'5, (tptr (Tstruct _qsbr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _map
    (Efield
      (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
        (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
  (Ssequence
    (Scall None
      (Evar _litehmap_lock (Tfunction
                             (Tcons (tptr (Tstruct _litemap noattr))
                               (Tcons (tptr (Tstruct _literef noattr)) Tnil))
                             tvoid cc_default))
      ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
       (Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _litehmap_load (Tfunction
                                 (Tcons (tptr (Tstruct _litemap noattr))
                                   Tnil) (tptr (Tstruct _litehmap noattr))
                                 cc_default))
          ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
        (Sset _hmap0 (Etempvar _t'1 (tptr (Tstruct _litehmap noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _litehmap_switch (Tfunction
                                     (Tcons (tptr (Tstruct _litemap noattr))
                                       (Tcons
                                         (tptr (Tstruct _litehmap noattr))
                                         Tnil))
                                     (tptr (Tstruct _litehmap noattr))
                                     cc_default))
            ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
             (Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) :: nil))
          (Sset _hmap1 (Etempvar _t'2 (tptr (Tstruct _litehmap noattr)))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _hmap0 (tptr (Tstruct _litehmap noattr)))
                    (Tstruct _litehmap noattr)) _nalloc tulong))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _hmap0 (tptr (Tstruct _litehmap noattr)))
                      (Tstruct _litehmap noattr)) _nkeys tulong))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tulong)
                               (Etempvar _t'9 tulong) tint)
                  (Sset _t'3 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _hmap1 (tptr (Tstruct _litehmap noattr)))
                          (Tstruct _litehmap noattr)) _nalloc tulong))
                    (Ssequence
                      (Sset _t'11
                        (Efield
                          (Ederef
                            (Etempvar _hmap1 (tptr (Tstruct _litehmap noattr)))
                            (Tstruct _litehmap noattr)) _nkeys tulong))
                      (Sset _t'3
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'10 tulong)
                            (Etempvar _t'11 tulong) tint) tbool)))))))
            (Sifthenelse (Etempvar _t'3 tint)
              (Ssequence
                (Scall None
                  (Evar _litehmap_unlock (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _litemap noattr))
                                             Tnil) tvoid cc_default))
                  ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
              Sskip))
          (Ssequence
            (Sset _leaf1
              (Efield
                (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _prev
                (tptr (Tstruct _liteleaf noattr))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _next
                  (tptr (Tstruct _liteleaf noattr)))
                (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                        (Tstruct _liteleaf noattr)) _next
                      (tptr (Tstruct _liteleaf noattr))))
                  (Sifthenelse (Etempvar _t'6 (tptr (Tstruct _liteleaf noattr)))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                            (Tstruct _liteleaf noattr)) _next
                          (tptr (Tstruct _liteleaf noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'7 (tptr (Tstruct _liteleaf noattr)))
                            (Tstruct _liteleaf noattr)) _prev
                          (tptr (Tstruct _liteleaf noattr)))
                        (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _litehmap_version_load (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _litehmap noattr))
                                                       Tnil) tulong
                                                     cc_default))
                      ((Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) ::
                       nil))
                    (Sset _v1
                      (Ebinop Oadd (Etempvar _t'4 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Scall None
                      (Evar _liteleaf_version_store (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _liteleaf noattr))
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                      ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                       (Etempvar _v1 tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _liteleaf_version_store (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _liteleaf noattr))
                                                          (Tcons tulong Tnil))
                                                        tvoid cc_default))
                        ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                         (Etempvar _v1 tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _litehmap_version_store (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _litehmap noattr))
                                                            (Tcons tulong
                                                              Tnil)) tvoid
                                                          cc_default))
                          ((Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                           (Etempvar _v1 tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _litemeta_split (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _litehmap noattr))
                                                      (Tcons
                                                        (tptr (Tstruct _liteleaf noattr))
                                                        Tnil)) tvoid
                                                    cc_default))
                            ((Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                             (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _qsbr_update (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _qsbr_ref noattr))
                                                     (Tcons tulong Tnil))
                                                   tvoid cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _ref (tptr (Tstruct _literef noattr)))
                                     (Tstruct _literef noattr)) _qref
                                   (Tstruct _qsbr_ref noattr))
                                 (tptr (Tstruct _qsbr_ref noattr))) ::
                               (Etempvar _v1 tulong) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _litehmap_store (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _litemap noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _litehmap noattr))
                                                            Tnil)) tvoid
                                                        cc_default))
                                ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                                 (Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                                 nil))
                              (Ssequence
                                (Scall None
                                  (Evar _liteleaf_unlock_write (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _liteleaf noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                  ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                                   nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _liteleaf_unlock_write (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                    ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'5
                                        (Efield
                                          (Ederef
                                            (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                            (Tstruct _litemap noattr)) _qsbr
                                          (tptr (Tstruct _qsbr noattr))))
                                      (Scall None
                                        (Evar _qsbr_wait (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _qsbr noattr))
                                                             (Tcons tulong
                                                               Tnil)) tvoid
                                                           cc_default))
                                        ((Etempvar _t'5 (tptr (Tstruct _qsbr noattr))) ::
                                         (Etempvar _v1 tulong) :: nil)))
                                    (Ssequence
                                      (Scall None
                                        (Evar _litemeta_split (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _litehmap noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                        ((Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) ::
                                         (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _litehmap_unlock (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _litemap noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                                           nil))
                                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))))))))))))))
|}.

Definition f_litemap_split_insert := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_leaf1, (tptr (Tstruct _liteleaf noattr))) :: (_i, tuint) ::
                (_new, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf2, (tptr (Tstruct _liteleaf noattr))) ::
               (_rsm, tbool) :: (_t'2, tbool) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'4, (tptr (Tstruct _litemap noattr))) ::
               (_t'3, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
            (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
      (Scall (Some _t'1)
        (Evar _litemap_split_leaf (Tfunction
                                    (Tcons (tptr (Tstruct _litemap noattr))
                                      (Tcons
                                        (tptr (Tstruct _liteleaf noattr))
                                        (Tcons tuint
                                          (Tcons (tptr (Tstruct _kv noattr))
                                            Tnil))))
                                    (tptr (Tstruct _liteleaf noattr))
                                    cc_default))
        ((Etempvar _t'4 (tptr (Tstruct _litemap noattr))) ::
         (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
         (Etempvar _i tuint) ::
         (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil)))
    (Sset _leaf2 (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Scall None
          (Evar _liteleaf_unlock_write (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _liteleaf noattr))
                                           Tnil) tvoid cc_default))
          ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint))))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _rwlock_lock_write (Tfunction
                                   (Tcons (tptr (Tunion __6333 noattr)) Tnil)
                                   tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
               (Tstruct _liteleaf noattr)) _leaflock (Tunion __6333 noattr))
           (tptr (Tunion __6333 noattr))) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _litemap_split_meta (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _literef noattr))
                                          (Tcons
                                            (tptr (Tstruct _liteleaf noattr))
                                            Tnil)) tbool cc_default))
            ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
             (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) :: nil))
          (Sset _rsm (Ecast (Etempvar _t'2 tbool) tbool)))
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _rsm tbool) tint)
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                      (Tstruct _literef noattr)) _map
                    (tptr (Tstruct _litemap noattr))))
                (Scall None
                  (Evar _liteleaf_split_undo (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _litemap noattr))
                                                 (Tcons
                                                   (tptr (Tstruct _liteleaf noattr))
                                                   (Tcons
                                                     (tptr (Tstruct _liteleaf noattr))
                                                     (Tcons tuint Tnil))))
                                               tvoid cc_default))
                  ((Etempvar _t'3 (tptr (Tstruct _litemap noattr))) ::
                   (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                   (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                   (Etempvar _i tuint) :: nil)))
              (Scall None
                (Evar _liteleaf_unlock_write (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _liteleaf noattr))
                                                 Tnil) tvoid cc_default))
                ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) :: nil)))
            Sskip)
          (Sreturn (Some (Etempvar _rsm tbool))))))))
|}.

Definition f_litemeta_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hmap, (tptr (Tstruct _litehmap noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tulong) ::
               (_t'8, (tptr (Tstruct _kv noattr))) ::
               (_t'7, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'6, (tptr (Tstruct __7144 noattr))) :: (_t'5, tulong) ::
               (_t'4, (tptr (Tstruct __7144 noattr))) ::
               (_t'3, (tptr (Tstruct __7144 noattr))) :: (_t'2, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _anchor (tptr (Tstruct _kv noattr))))
      (Scall (Some _t'1)
        (Evar _litehmap_seek_ge (Tfunction
                                  (Tcons (tptr (Tstruct _litehmap noattr))
                                    (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                                  tulong cc_default))
        ((Etempvar _hmap (tptr (Tstruct _litehmap noattr))) ::
         (Etempvar _t'8 (tptr (Tstruct _kv noattr))) :: nil)))
    (Sset _i (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
            (Tstruct _litehmap noattr)) _pairs
          (tptr (Tstruct __7144 noattr))))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef
              (Ebinop Oadd (Etempvar _t'6 (tptr (Tstruct __7144 noattr)))
                (Etempvar _i tulong) (tptr (Tstruct __7144 noattr)))
              (Tstruct __7144 noattr)) _leaf
            (tptr (Tstruct _liteleaf noattr))))
        (Scall None
          (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
          ((Ebinop Oeq (Etempvar _t'7 (tptr (Tstruct _liteleaf noattr)))
             (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) tint) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
              (Tstruct _litehmap noattr)) _pairs
            (tptr (Tstruct __7144 noattr))))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                (Tstruct _litehmap noattr)) _pairs
              (tptr (Tstruct __7144 noattr))))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                  (Tstruct _litehmap noattr)) _nkeys tulong))
            (Scall None
              (Evar _memmove (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                               (tptr tvoid) cc_default))
              ((Ebinop Oadd (Etempvar _t'3 (tptr (Tstruct __7144 noattr)))
                 (Etempvar _i tulong) (tptr (Tstruct __7144 noattr))) ::
               (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct __7144 noattr)))
                 (Ebinop Oadd (Etempvar _i tulong)
                   (Econst_int (Int.repr 1) tint) tulong)
                 (tptr (Tstruct __7144 noattr))) ::
               (Ebinop Omul (Esizeof (Tstruct __7144 noattr) tulong)
                 (Ebinop Osub
                   (Ebinop Osub (Etempvar _t'5 tulong) (Etempvar _i tulong)
                     tulong) (Econst_int (Int.repr 1) tint) tulong) tulong) ::
               nil)))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
              (Tstruct _litehmap noattr)) _nkeys tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
              (Tstruct _litehmap noattr)) _nkeys tulong)
          (Ebinop Osub (Etempvar _t'2 tulong) (Econst_int (Int.repr 1) tint)
            tulong))))))
|}.

Definition f_litemap_meta_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_leaf1, (tptr (Tstruct _liteleaf noattr))) ::
                (_leaf2, (tptr (Tstruct _liteleaf noattr))) ::
                (_unlock_leaf1, tbool) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_hmap0, (tptr (Tstruct _litehmap noattr))) ::
               (_hmap1, (tptr (Tstruct _litehmap noattr))) ::
               (_v1, tulong) :: (_t'3, tulong) ::
               (_t'2, (tptr (Tstruct _litehmap noattr))) ::
               (_t'1, (tptr (Tstruct _litehmap noattr))) ::
               (_t'10, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'9, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'8, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'7, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'6, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'5, (tptr (Tstruct _qsbr noattr))) ::
               (_t'4, (tptr (Tstruct _slab noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'10
      (Efield
        (Ederef (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
          (Tstruct _liteleaf noattr)) _next
        (tptr (Tstruct _liteleaf noattr))))
    (Scall None
      (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
      ((Ebinop Oeq (Etempvar _t'10 (tptr (Tstruct _liteleaf noattr)))
         (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) tint) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _prev
          (tptr (Tstruct _liteleaf noattr))))
      (Scall None
        (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
        ((Ebinop Oeq (Etempvar _t'9 (tptr (Tstruct _liteleaf noattr)))
           (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) tint) :: nil)))
    (Ssequence
      (Sset _map
        (Efield
          (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
            (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
      (Ssequence
        (Scall None
          (Evar _litehmap_lock (Tfunction
                                 (Tcons (tptr (Tstruct _litemap noattr))
                                   (Tcons (tptr (Tstruct _literef noattr))
                                     Tnil)) tvoid cc_default))
          ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
           (Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _litehmap_load (Tfunction
                                     (Tcons (tptr (Tstruct _litemap noattr))
                                       Tnil)
                                     (tptr (Tstruct _litehmap noattr))
                                     cc_default))
              ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
            (Sset _hmap0 (Etempvar _t'1 (tptr (Tstruct _litehmap noattr)))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _litehmap_switch (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _litemap noattr))
                                           (Tcons
                                             (tptr (Tstruct _litehmap noattr))
                                             Tnil))
                                         (tptr (Tstruct _litehmap noattr))
                                         cc_default))
                ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                 (Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) :: nil))
              (Sset _hmap1 (Etempvar _t'2 (tptr (Tstruct _litehmap noattr)))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _litehmap_version_load (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _litehmap noattr))
                                                   Tnil) tulong cc_default))
                  ((Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) ::
                   nil))
                (Sset _v1
                  (Ebinop Oadd (Etempvar _t'3 tulong)
                    (Econst_int (Int.repr 1) tint) tulong)))
              (Ssequence
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef
                        (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                        (Tstruct _liteleaf noattr)) _next
                      (tptr (Tstruct _liteleaf noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))
                        (Tstruct _liteleaf noattr)) _next
                      (tptr (Tstruct _liteleaf noattr)))
                    (Etempvar _t'8 (tptr (Tstruct _liteleaf noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                          (Tstruct _liteleaf noattr)) _next
                        (tptr (Tstruct _liteleaf noattr))))
                    (Sifthenelse (Etempvar _t'6 (tptr (Tstruct _liteleaf noattr)))
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr)))
                              (Tstruct _liteleaf noattr)) _next
                            (tptr (Tstruct _liteleaf noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _t'7 (tptr (Tstruct _liteleaf noattr)))
                              (Tstruct _liteleaf noattr)) _prev
                            (tptr (Tstruct _liteleaf noattr)))
                          (Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr)))))
                      Sskip))
                  (Ssequence
                    (Scall None
                      (Evar _liteleaf_version_store (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _liteleaf noattr))
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                      ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                       (Etempvar _v1 tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _liteleaf_version_store (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _liteleaf noattr))
                                                          (Tcons tulong Tnil))
                                                        tvoid cc_default))
                        ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                         (Etempvar _v1 tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _litehmap_version_store (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _litehmap noattr))
                                                            (Tcons tulong
                                                              Tnil)) tvoid
                                                          cc_default))
                          ((Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                           (Etempvar _v1 tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _litemeta_merge (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _litehmap noattr))
                                                      (Tcons
                                                        (tptr (Tstruct _liteleaf noattr))
                                                        Tnil)) tvoid
                                                    cc_default))
                            ((Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                             (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _qsbr_update (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _qsbr_ref noattr))
                                                     (Tcons tulong Tnil))
                                                   tvoid cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _ref (tptr (Tstruct _literef noattr)))
                                     (Tstruct _literef noattr)) _qref
                                   (Tstruct _qsbr_ref noattr))
                                 (tptr (Tstruct _qsbr_ref noattr))) ::
                               (Etempvar _v1 tulong) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _litehmap_store (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _litemap noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _litehmap noattr))
                                                            Tnil)) tvoid
                                                        cc_default))
                                ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                                 (Etempvar _hmap1 (tptr (Tstruct _litehmap noattr))) ::
                                 nil))
                              (Ssequence
                                (Sifthenelse (Etempvar _unlock_leaf1 tbool)
                                  (Scall None
                                    (Evar _liteleaf_unlock_write (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                    ((Etempvar _leaf1 (tptr (Tstruct _liteleaf noattr))) ::
                                     nil))
                                  Sskip)
                                (Ssequence
                                  (Scall None
                                    (Evar _liteleaf_unlock_write (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                    ((Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'5
                                        (Efield
                                          (Ederef
                                            (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                            (Tstruct _litemap noattr)) _qsbr
                                          (tptr (Tstruct _qsbr noattr))))
                                      (Scall None
                                        (Evar _qsbr_wait (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _qsbr noattr))
                                                             (Tcons tulong
                                                               Tnil)) tvoid
                                                           cc_default))
                                        ((Etempvar _t'5 (tptr (Tstruct _qsbr noattr))) ::
                                         (Etempvar _v1 tulong) :: nil)))
                                    (Ssequence
                                      (Scall None
                                        (Evar _litemeta_merge (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _litehmap noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                        ((Etempvar _hmap0 (tptr (Tstruct _litehmap noattr))) ::
                                         (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'4
                                            (Efield
                                              (Ederef
                                                (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                                (Tstruct _litemap noattr))
                                              _slab_leaf
                                              (tptr (Tstruct _slab noattr))))
                                          (Scall None
                                            (Evar _liteleaf_free (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _slab noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _liteleaf noattr))
                                                                    Tnil))
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _t'4 (tptr (Tstruct _slab noattr))) ::
                                             (Etempvar _leaf2 (tptr (Tstruct _liteleaf noattr))) ::
                                             nil)))
                                        (Scall None
                                          (Evar _litehmap_unlock (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _litemap noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
                                           nil))))))))))))))))))))))
|}.

Definition f_litemap_meta_leaf_merge := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, (tptr (Tstruct _liteleaf noattr))) :: (_t'1, tbool) ::
               (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _next
    (Efield
      (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
        (Tstruct _liteleaf noattr)) _next (tptr (Tstruct _liteleaf noattr))))
  (Ssequence
    (Scall None
      (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
      ((Etempvar _next (tptr (Tstruct _liteleaf noattr))) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _next (tptr (Tstruct _liteleaf noattr)))
                (Tstruct _liteleaf noattr)) _nr_keys tuint))
          (Sifthenelse (Ebinop Ole
                         (Ebinop Oadd (Etempvar _t'2 tuint)
                           (Etempvar _t'3 tuint) tuint)
                         (Econst_int (Int.repr 128) tuint) tint)
            (Ssequence
              (Scall (Some _t'1)
                (Evar _liteleaf_merge (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          (Tcons
                                            (tptr (Tstruct _liteleaf noattr))
                                            Tnil)) tbool cc_default))
                ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                 (Etempvar _next (tptr (Tstruct _liteleaf noattr))) :: nil))
              (Sifthenelse (Etempvar _t'1 tbool)
                (Ssequence
                  (Scall None
                    (Evar _litemap_meta_merge (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _literef noattr))
                                                  (Tcons
                                                    (tptr (Tstruct _liteleaf noattr))
                                                    (Tcons
                                                      (tptr (Tstruct _liteleaf noattr))
                                                      (Tcons tbool Tnil))))
                                                tvoid cc_default))
                    ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
                     (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                     (Etempvar _next (tptr (Tstruct _liteleaf noattr))) ::
                     (Econst_int (Int.repr 1) tint) :: nil))
                  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
                Sskip))
            Sskip)))
      (Ssequence
        (Scall None
          (Evar _liteleaf_unlock_write (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _liteleaf noattr))
                                           Tnil) tvoid cc_default))
          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _liteleaf_unlock_write (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _liteleaf noattr))
                                             Tnil) tvoid cc_default))
            ((Etempvar _next (tptr (Tstruct _liteleaf noattr))) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_litemap_put := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_kv__1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := ((_kref__1, (Tstruct _kref noattr)) ::
              (__res, (Tstruct _kref noattr)) :: nil);
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_new, (tptr (Tstruct _kv noattr))) ::
               (_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_im, tuint) ::
               (_i, tuint) :: (_old, (tptr (Tstruct _kv noattr))) ::
               (_rsi, tbool) :: (_t'5, tbool) ::
               (_t'4, (tptr (Tstruct _kv noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) ::
               (_t'12, (tptr tvoid)) ::
               (_t'11,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr tvoid) Tnil))
                        (tptr (Tstruct _kv noattr)) cc_default))) ::
               (_t'10, (tptr tvoid)) ::
               (_t'9,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr tvoid) Tnil)) tvoid cc_default))) ::
               (_t'8, tuint) :: (_t'7, (tptr tvoid)) ::
               (_t'6,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr tvoid) Tnil)) tvoid cc_default))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _map
    (Efield
      (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
        (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Efield
              (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                (Tstruct _litemap noattr)) _mm (Tstruct _kvmap_mm noattr))
            _in
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _kv noattr))
                      (Tcons (tptr tvoid) Tnil)) (tptr (Tstruct _kv noattr))
                    cc_default))))
        (Ssequence
          (Sset _t'12
            (Efield
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _mm (Tstruct _kvmap_mm noattr))
              _priv (tptr tvoid)))
          (Scall (Some _t'1)
            (Etempvar _t'11 (tptr (Tfunction
                                    (Tcons (tptr (Tstruct _kv noattr))
                                      (Tcons (tptr tvoid) Tnil))
                                    (tptr (Tstruct _kv noattr)) cc_default)))
            ((Etempvar _kv__1 (tptr (Tstruct _kv noattr))) ::
             (Etempvar _t'12 (tptr tvoid)) :: nil))))
      (Sset _new (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _new (tptr (Tstruct _kv noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall None
            (Evar _kv_kref (Tfunction
                             (Tcons (tptr (Tstruct _kref noattr))
                               (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                             tvoid
                             {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
            ((Eaddrof (Evar __res (Tstruct _kref noattr))
               (tptr (Tstruct _kref noattr))) ::
             (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil))
          (Sassign (Evar _kref__1 (Tstruct _kref noattr))
            (Evar __res (Tstruct _kref noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _litemap_jump_leaf_write (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _literef noattr))
                                                 (Tcons
                                                   (tptr (Tstruct _kref noattr))
                                                   Tnil))
                                               (tptr (Tstruct _liteleaf noattr))
                                               cc_default))
              ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
               (Eaddrof (Evar _kref__1 (Tstruct _kref noattr))
                 (tptr (Tstruct _kref noattr))) :: nil))
            (Sset _leaf (Etempvar _t'2 (tptr (Tstruct _liteleaf noattr)))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _liteleaf_seek_ge (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _liteleaf noattr))
                                            (Tcons
                                              (tptr (Tstruct _kref noattr))
                                              Tnil)) tuint cc_default))
                ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                 (Eaddrof (Evar _kref__1 (Tstruct _kref noattr))
                   (tptr (Tstruct _kref noattr))) :: nil))
              (Sset _im (Etempvar _t'3 tuint)))
            (Ssequence
              (Sset _i
                (Ebinop Oand (Etempvar _im tuint)
                  (Ebinop Osub (Econst_int (Int.repr 128) tuint)
                    (Econst_int (Int.repr 1) tint) tuint) tuint))
              (Ssequence
                (Sifthenelse (Ebinop Oshr (Etempvar _im tuint)
                               (Econst_int (Int.repr 31) tint) tuint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _liteleaf_update (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _liteleaf noattr))
                                                   (Tcons tuint
                                                     (Tcons
                                                       (tptr (Tstruct _kv noattr))
                                                       Tnil)))
                                                 (tptr (Tstruct _kv noattr))
                                                 cc_default))
                        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                         (Etempvar _i tuint) ::
                         (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil))
                      (Sset _old (Etempvar _t'4 (tptr (Tstruct _kv noattr)))))
                    (Ssequence
                      (Scall None
                        (Evar _liteleaf_unlock_write (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _liteleaf noattr))
                                                         Tnil) tvoid
                                                       cc_default))
                        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                         nil))
                      (Ssequence
                        (Ssequence
                          (Sset _t'9
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                  (Tstruct _litemap noattr)) _mm
                                (Tstruct _kvmap_mm noattr)) _free
                              (tptr (Tfunction
                                      (Tcons (tptr (Tstruct _kv noattr))
                                        (Tcons (tptr tvoid) Tnil)) tvoid
                                      cc_default))))
                          (Ssequence
                            (Sset _t'10
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                    (Tstruct _litemap noattr)) _mm
                                  (Tstruct _kvmap_mm noattr)) _priv
                                (tptr tvoid)))
                            (Scall None
                              (Etempvar _t'9 (tptr (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _kv noattr))
                                                       (Tcons (tptr tvoid)
                                                         Tnil)) tvoid
                                                     cc_default)))
                              ((Etempvar _old (tptr (Tstruct _kv noattr))) ::
                               (Etempvar _t'10 (tptr tvoid)) :: nil))))
                        (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                          (Tstruct _liteleaf noattr)) _nr_keys tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'8 tuint)
                                   (Econst_int (Int.repr 128) tuint) tint)
                      (Ssequence
                        (Scall None
                          (Evar _liteleaf_insert (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _liteleaf noattr))
                                                     (Tcons tuint
                                                       (Tcons
                                                         (tptr (Tstruct _kv noattr))
                                                         Tnil))) tvoid
                                                   cc_default))
                          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                           (Etempvar _i tuint) ::
                           (Etempvar _new (tptr (Tstruct _kv noattr))) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _liteleaf_unlock_write (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _liteleaf noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                            ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                             nil))
                          (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _litemap_split_insert (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _literef noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _liteleaf noattr))
                                                          (Tcons tuint
                                                            (Tcons
                                                              (tptr (Tstruct _kv noattr))
                                                              Tnil)))) tbool
                                                      cc_default))
                        ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
                         (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
                         (Etempvar _i tuint) ::
                         (Etempvar _new (tptr (Tstruct _kv noattr))) :: nil))
                      (Sset _rsi (Ecast (Etempvar _t'5 tbool) tbool)))
                    (Ssequence
                      (Sifthenelse (Eunop Onotbool (Etempvar _rsi tbool)
                                     tint)
                        (Ssequence
                          (Sset _t'6
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                  (Tstruct _litemap noattr)) _mm
                                (Tstruct _kvmap_mm noattr)) _free
                              (tptr (Tfunction
                                      (Tcons (tptr (Tstruct _kv noattr))
                                        (Tcons (tptr tvoid) Tnil)) tvoid
                                      cc_default))))
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _map (tptr (Tstruct _litemap noattr)))
                                    (Tstruct _litemap noattr)) _mm
                                  (Tstruct _kvmap_mm noattr)) _priv
                                (tptr tvoid)))
                            (Scall None
                              (Etempvar _t'6 (tptr (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _kv noattr))
                                                       (Tcons (tptr tvoid)
                                                         Tnil)) tvoid
                                                     cc_default)))
                              ((Etempvar _new (tptr (Tstruct _kv noattr))) ::
                               (Etempvar _t'7 (tptr tvoid)) :: nil))))
                        Sskip)
                      (Sreturn (Some (Etempvar _rsi tbool))))))))))))))
|}.

Definition f_litemap_del_try_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, (tptr (Tstruct _liteleaf noattr))) :: (_t'1, tint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _next
    (Efield
      (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
        (Tstruct _liteleaf noattr)) _next (tptr (Tstruct _liteleaf noattr))))
  (Ssequence
    (Sifthenelse (Etempvar _next (tptr (Tstruct _liteleaf noattr)))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _nr_keys tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'1 (Ecast (Econst_int (Int.repr 1) tint) tbool))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _nr_keys tuint))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _next (tptr (Tstruct _liteleaf noattr)))
                      (Tstruct _liteleaf noattr)) _nr_keys tuint))
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt
                      (Ebinop Oadd (Etempvar _t'3 tuint)
                        (Etempvar _t'4 tuint) tuint)
                      (Ebinop Oshr
                        (Ebinop Oadd (Econst_int (Int.repr 128) tuint)
                          (Ebinop Oshr (Econst_int (Int.repr 128) tuint)
                            (Econst_int (Int.repr 1) tint) tuint) tuint)
                        (Econst_int (Int.repr 1) tint) tuint) tint) tbool))))
            (Sset _t'1 (Ecast (Etempvar _t'1 tint) tbool)))))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Scall None
          (Evar _liteleaf_lock_write (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _liteleaf noattr))
                                         (Tcons
                                           (tptr (Tstruct _literef noattr))
                                           Tnil)) tvoid cc_default))
          ((Etempvar _next (tptr (Tstruct _liteleaf noattr))) ::
           (Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
        (Scall None
          (Evar _litemap_meta_leaf_merge (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _literef noattr))
                                             (Tcons
                                               (tptr (Tstruct _liteleaf noattr))
                                               Tnil)) tbool cc_default))
          ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
           (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil)))
      (Scall None
        (Evar _liteleaf_unlock_write (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _liteleaf noattr))
                                         Tnil) tvoid cc_default))
        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil)))))
|}.

Definition f_litemap_del := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_im, tuint) ::
               (_kv__1, (tptr (Tstruct _kv noattr))) ::
               (_map, (tptr (Tstruct _litemap noattr))) ::
               (_t'3, (tptr (Tstruct _kv noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'5, (tptr tvoid)) ::
               (_t'4,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr tvoid) Tnil)) tvoid cc_default))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_jump_leaf_write (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _literef noattr))
                                         (Tcons (tptr (Tstruct _kref noattr))
                                           Tnil))
                                       (tptr (Tstruct _liteleaf noattr))
                                       cc_default))
      ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
       (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
    (Sset _leaf (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _liteleaf_match_i (Tfunction
                                  (Tcons (tptr (Tstruct _liteleaf noattr))
                                    (Tcons (tptr (Tstruct _kref noattr))
                                      Tnil)) tuint cc_default))
        ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
         (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
      (Sset _im (Etempvar _t'2 tuint)))
    (Sifthenelse (Ebinop Olt (Etempvar _im tuint)
                   (Econst_int (Int.repr 128) tuint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _liteleaf_remove (Tfunction
                                     (Tcons (tptr (Tstruct _liteleaf noattr))
                                       (Tcons tuint Tnil))
                                     (tptr (Tstruct _kv noattr)) cc_default))
            ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
             (Etempvar _im tuint) :: nil))
          (Sset _kv__1 (Etempvar _t'3 (tptr (Tstruct _kv noattr)))))
        (Ssequence
          (Scall None
            (Evar _litemap_del_try_merge (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _literef noattr))
                                             (Tcons
                                               (tptr (Tstruct _liteleaf noattr))
                                               Tnil)) tvoid cc_default))
            ((Etempvar _ref (tptr (Tstruct _literef noattr))) ::
             (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid
                                    cc_default))
              ((Etempvar _kv__1 (tptr (Tstruct _kv noattr))) :: nil))
            (Ssequence
              (Sset _map
                (Efield
                  (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                    (Tstruct _literef noattr)) _map
                  (tptr (Tstruct _litemap noattr))))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _map (tptr (Tstruct _litemap noattr)))
                          (Tstruct _litemap noattr)) _mm
                        (Tstruct _kvmap_mm noattr)) _free
                      (tptr (Tfunction
                              (Tcons (tptr (Tstruct _kv noattr))
                                (Tcons (tptr tvoid) Tnil)) tvoid cc_default))))
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _map (tptr (Tstruct _litemap noattr)))
                            (Tstruct _litemap noattr)) _mm
                          (Tstruct _kvmap_mm noattr)) _priv (tptr tvoid)))
                    (Scall None
                      (Etempvar _t'4 (tptr (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _kv noattr))
                                               (Tcons (tptr tvoid) Tnil))
                                             tvoid cc_default)))
                      ((Etempvar _kv__1 (tptr (Tstruct _kv noattr))) ::
                       (Etempvar _t'5 (tptr tvoid)) :: nil))))
                (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
      (Ssequence
        (Scall None
          (Evar _liteleaf_unlock_write (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _liteleaf noattr))
                                           Tnil) tvoid cc_default))
          ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_litemap_iter_create := {|
  fn_return := (tptr (Tstruct _litemap_iter noattr));
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _litemap_iter noattr) tulong) :: nil))
    (Sset _iter (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
            (Tstruct _litemap_iter noattr)) _ref
          (tptr (Tstruct _literef noattr)))
        (Etempvar _ref (tptr (Tstruct _literef noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                (Tstruct _literef noattr)) _map
              (tptr (Tstruct _litemap noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _map
              (tptr (Tstruct _litemap noattr)))
            (Etempvar _t'2 (tptr (Tstruct _litemap noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _is tuint)
              (Econst_int (Int.repr 0) tint))
            (Sreturn (Some (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))))))))))
|}.

Definition f_litemap_iter_fix := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, (tptr (Tstruct _liteleaf noattr))) ::
               (_ref, (tptr (Tstruct _literef noattr))) :: (_t'2, tbool) ::
               (_t'1, tbool) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _liteleaf noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'4, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'3, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_valid (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _litemap_iter noattr))
                                    Tnil) tbool cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn None)
      Sskip))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _is tuint))
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr))))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _t'7 (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _nr_keys tuint))
            (Sifthenelse (Ebinop Oge (Etempvar _t'6 tuint)
                           (Etempvar _t'8 tuint) tint)
              Sskip
              Sbreak))))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr))))
          (Sset _next
            (Efield
              (Ederef (Etempvar _t'5 (tptr (Tstruct _liteleaf noattr)))
                (Tstruct _liteleaf noattr)) _next
              (tptr (Tstruct _liteleaf noattr)))))
        (Ssequence
          (Sifthenelse (Ebinop One
                         (Etempvar _next (tptr (Tstruct _liteleaf noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Sset _ref
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _ref
                  (tptr (Tstruct _literef noattr))))
              (Ssequence
                (Scall None
                  (Evar _liteleaf_lock_read (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _liteleaf noattr))
                                                (Tcons
                                                  (tptr (Tstruct _literef noattr))
                                                  Tnil)) tvoid cc_default))
                  ((Etempvar _next (tptr (Tstruct _liteleaf noattr))) ::
                   (Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                        (Tstruct _litemap_iter noattr)) _leaf
                      (tptr (Tstruct _liteleaf noattr))))
                  (Scall None
                    (Evar _liteleaf_unlock_read (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _liteleaf noattr))
                                                    Tnil) tvoid cc_default))
                    ((Etempvar _t'4 (tptr (Tstruct _liteleaf noattr))) ::
                     nil)))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _leaf
                  (tptr (Tstruct _liteleaf noattr))))
              (Scall None
                (Evar _liteleaf_unlock_read (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _liteleaf noattr))
                                                Tnil) tvoid cc_default))
                ((Etempvar _t'3 (tptr (Tstruct _liteleaf noattr))) :: nil))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _leaf
                (tptr (Tstruct _liteleaf noattr)))
              (Etempvar _next (tptr (Tstruct _liteleaf noattr))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _is tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _litemap_iter_valid (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _litemap_iter noattr))
                                                Tnil) tbool cc_default))
                  ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) ::
                   nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tbool) tint)
                  (Sreturn None)
                  Sskip)))))))
    Sskip))
|}.

Definition f_litemap_iter_seek := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_key, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'5, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'4, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'3, (tptr (Tstruct _literef noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid cc_default))
    ((Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
            (Tstruct _litemap_iter noattr)) _leaf
          (tptr (Tstruct _liteleaf noattr))))
      (Sifthenelse (Etempvar _t'4 (tptr (Tstruct _liteleaf noattr)))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr))))
          (Scall None
            (Evar _liteleaf_unlock_read (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _liteleaf noattr))
                                            Tnil) tvoid cc_default))
            ((Etempvar _t'5 (tptr (Tstruct _liteleaf noattr))) :: nil)))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _ref
              (tptr (Tstruct _literef noattr))))
          (Scall (Some _t'1)
            (Evar _litemap_jump_leaf_read (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _literef noattr))
                                              (Tcons
                                                (tptr (Tstruct _kref noattr))
                                                Tnil))
                                            (tptr (Tstruct _liteleaf noattr))
                                            cc_default))
            ((Etempvar _t'3 (tptr (Tstruct _literef noattr))) ::
             (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil)))
        (Sset _leaf (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _leaf
            (tptr (Tstruct _liteleaf noattr)))
          (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _liteleaf_seek_ge (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          (Tcons
                                            (tptr (Tstruct _kref noattr))
                                            Tnil)) tuint cc_default))
              ((Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) ::
               (Etempvar _key (tptr (Tstruct _kref noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _is tuint)
              (Etempvar _t'2 tuint)))
          (Scall None
            (Evar _litemap_iter_fix (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _litemap_iter noattr))
                                        Tnil) tvoid cc_default))
            ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil)))))))
|}.

Definition f_litemap_iter_valid := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
        (Tstruct _litemap_iter noattr)) _leaf
      (tptr (Tstruct _liteleaf noattr))))
  (Sreturn (Some (Ebinop One
                   (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_litemap_iter_current := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) :: (_t'1, tbool) ::
               (_t'6, tuint) :: (_t'5, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_valid (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _litemap_iter noattr))
                                    Tnil) tbool cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tbool)
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _is tuint))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _leaf
                (tptr (Tstruct _liteleaf noattr))))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _t'5 (tptr (Tstruct _liteleaf noattr)))
                    (Tstruct _liteleaf noattr)) _nr_keys tuint))
              (Scall None
                (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid
                                      cc_default))
                ((Ebinop Olt (Etempvar _t'4 tuint) (Etempvar _t'6 tuint)
                   tint) :: nil)))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _leaf
                (tptr (Tstruct _liteleaf noattr))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _is tuint))
              (Sset _kv__1
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _t'2 (tptr (Tstruct _liteleaf noattr)))
                        (Tstruct _liteleaf noattr)) _kvs
                      (tarray (tptr (Tstruct _kv noattr)) 128))
                    (Etempvar _t'3 tuint) (tptr (tptr (Tstruct _kv noattr))))
                  (tptr (Tstruct _kv noattr))))))
          (Sreturn (Some (Etempvar _kv__1 (tptr (Tstruct _kv noattr)))))))
      Sskip))
  (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|}.

Definition f_litemap_iter_peek := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_out, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) ::
               (_ret, (tptr (Tstruct _kv noattr))) ::
               (_t'2, (tptr (Tstruct _kv noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) ::
               (_t'4,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                        (tptr (Tstruct _kv noattr)) cc_default))) ::
               (_t'3, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_current (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _litemap_iter noattr))
                                      Tnil) (tptr (Tstruct _kv noattr))
                                    cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sset _kv__1 (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
  (Ssequence
    (Sifthenelse (Etempvar _kv__1 (tptr (Tstruct _kv noattr)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                  (Tstruct _litemap_iter noattr)) _map
                (tptr (Tstruct _litemap noattr))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _litemap noattr)))
                      (Tstruct _litemap noattr)) _mm
                    (Tstruct _kvmap_mm noattr)) _out
                  (tptr (Tfunction
                          (Tcons (tptr (Tstruct _kv noattr))
                            (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                          (tptr (Tstruct _kv noattr)) cc_default))))
              (Scall (Some _t'2)
                (Etempvar _t'4 (tptr (Tfunction
                                       (Tcons (tptr (Tstruct _kv noattr))
                                         (Tcons (tptr (Tstruct _kv noattr))
                                           Tnil)) (tptr (Tstruct _kv noattr))
                                       cc_default)))
                ((Etempvar _kv__1 (tptr (Tstruct _kv noattr))) ::
                 (Etempvar _out (tptr (Tstruct _kv noattr))) :: nil))))
          (Sset _ret (Etempvar _t'2 (tptr (Tstruct _kv noattr)))))
        (Sreturn (Some (Etempvar _ret (tptr (Tstruct _kv noattr))))))
      Sskip)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
|}.

Definition f_litemap_iter_kref := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_kref__1, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_current (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _litemap_iter noattr))
                                      Tnil) (tptr (Tstruct _kv noattr))
                                    cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sset _kv__1 (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
  (Ssequence
    (Sifthenelse (Etempvar _kv__1 (tptr (Tstruct _kv noattr)))
      (Ssequence
        (Scall None
          (Evar _kref_ref_kv (Tfunction
                               (Tcons (tptr (Tstruct _kref noattr))
                                 (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                               tvoid cc_default))
          ((Etempvar _kref__1 (tptr (Tstruct _kref noattr))) ::
           (Etempvar _kv__1 (tptr (Tstruct _kv noattr))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
      Sskip)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_litemap_iter_kvref := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_kvref__1, (tptr (Tstruct _kvref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_current (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _litemap_iter noattr))
                                      Tnil) (tptr (Tstruct _kv noattr))
                                    cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sset _kv__1 (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
  (Ssequence
    (Sifthenelse (Etempvar _kv__1 (tptr (Tstruct _kv noattr)))
      (Ssequence
        (Scall None
          (Evar _kvref_ref_kv (Tfunction
                                (Tcons (tptr (Tstruct _kvref noattr))
                                  (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                                tvoid cc_default))
          ((Etempvar _kvref__1 (tptr (Tstruct _kvref noattr))) ::
           (Etempvar _kv__1 (tptr (Tstruct _kv noattr))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
      Sskip)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_litemap_iter_skip1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _litemap_iter_valid (Tfunction
                                (Tcons (tptr (Tstruct _litemap_iter noattr))
                                  Tnil) tbool cc_default))
    ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
  (Sifthenelse (Etempvar _t'1 tbool)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _is tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _is tuint)
          (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      (Scall None
        (Evar _litemap_iter_fix (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _litemap_iter noattr))
                                    Tnil) tvoid cc_default))
        ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil)))
    Sskip))
|}.

Definition f_litemap_iter_skip := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_nr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_todo, tuint) :: (_cap, tuint) :: (_nskip, tuint) ::
               (_t'3, tuint) :: (_t'2, tbool) :: (_t'1, tint) ::
               (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _liteleaf noattr))) :: (_t'4, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _todo (Etempvar _nr tuint))
  (Sloop
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _todo tuint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _litemap_iter_valid (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _litemap_iter noattr))
                                            Tnil) tbool cc_default))
              ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
            (Sset _t'1 (Ecast (Etempvar _t'2 tbool) tbool)))
          (Sset _t'1 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                (Tstruct _litemap_iter noattr)) _leaf
              (tptr (Tstruct _liteleaf noattr))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _t'5 (tptr (Tstruct _liteleaf noattr)))
                  (Tstruct _liteleaf noattr)) _nr_keys tuint))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _is tuint))
              (Sset _cap
                (Ebinop Osub (Etempvar _t'6 tuint) (Etempvar _t'7 tuint)
                  tuint)))))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _cap tuint)
                           (Etempvar _todo tuint) tint)
              (Sset _t'3 (Ecast (Etempvar _cap tuint) tuint))
              (Sset _t'3 (Ecast (Etempvar _todo tuint) tuint)))
            (Sset _nskip (Etempvar _t'3 tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _is tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
                    (Tstruct _litemap_iter noattr)) _is tuint)
                (Ebinop Oadd (Etempvar _t'4 tuint) (Etempvar _nskip tuint)
                  tuint)))
            (Ssequence
              (Scall None
                (Evar _litemap_iter_fix (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _litemap_iter noattr))
                                            Tnil) tvoid cc_default))
                ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) ::
                 nil))
              (Sset _todo
                (Ebinop Osub (Etempvar _todo tuint) (Etempvar _nskip tuint)
                  tuint)))))))
    Sskip))
|}.

Definition f_litemap_iter_next := {|
  fn_return := (tptr (Tstruct _kv noattr));
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_out, (tptr (Tstruct _kv noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, (tptr (Tstruct _kv noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_peek (Tfunction
                                 (Tcons (tptr (Tstruct _litemap_iter noattr))
                                   (Tcons (tptr (Tstruct _kv noattr)) Tnil))
                                 (tptr (Tstruct _kv noattr)) cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) ::
       (Etempvar _out (tptr (Tstruct _kv noattr))) :: nil))
    (Sset _ret (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
  (Ssequence
    (Scall None
      (Evar _litemap_iter_skip1 (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _litemap_iter noattr))
                                    Tnil) tvoid cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sreturn (Some (Etempvar _ret (tptr (Tstruct _kv noattr)))))))
|}.

Definition f_litemap_iter_inp := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) ::
                (_uf,
                 (tptr (Tfunction
                         (Tcons (tptr (Tstruct _kv noattr))
                           (Tcons (tptr tvoid) Tnil)) tvoid cc_default))) ::
                (_priv, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_kv__1, (tptr (Tstruct _kv noattr))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _litemap_iter_current (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _litemap_iter noattr))
                                      Tnil) (tptr (Tstruct _kv noattr))
                                    cc_default))
      ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil))
    (Sset _kv__1 (Etempvar _t'1 (tptr (Tstruct _kv noattr)))))
  (Ssequence
    (Scall None
      (Etempvar _uf (tptr (Tfunction
                            (Tcons (tptr (Tstruct _kv noattr))
                              (Tcons (tptr tvoid) Tnil)) tvoid cc_default)))
      ((Etempvar _kv__1 (tptr (Tstruct _kv noattr))) ::
       (Etempvar _priv (tptr tvoid)) :: nil))
    (Sreturn (Some (Ebinop One (Etempvar _kv__1 (tptr (Tstruct _kv noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)))))
|}.

Definition f_litemap_iter_park := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
        (Tstruct _litemap_iter noattr)) _leaf
      (tptr (Tstruct _liteleaf noattr))))
  (Sifthenelse (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _leaf
            (tptr (Tstruct _liteleaf noattr))))
        (Scall None
          (Evar _liteleaf_unlock_read (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          Tnil) tvoid cc_default))
          ((Etempvar _t'2 (tptr (Tstruct _liteleaf noattr))) :: nil)))
      (Sassign
        (Efield
          (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
            (Tstruct _litemap_iter noattr)) _leaf
          (tptr (Tstruct _liteleaf noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip))
|}.

Definition f_litemap_iter_destroy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_iter, (tptr (Tstruct _litemap_iter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
          (Tstruct _litemap_iter noattr)) _leaf
        (tptr (Tstruct _liteleaf noattr))))
    (Sifthenelse (Etempvar _t'1 (tptr (Tstruct _liteleaf noattr)))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _iter (tptr (Tstruct _litemap_iter noattr)))
              (Tstruct _litemap_iter noattr)) _leaf
            (tptr (Tstruct _liteleaf noattr))))
        (Scall None
          (Evar _liteleaf_unlock_read (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _liteleaf noattr))
                                          Tnil) tvoid cc_default))
          ((Etempvar _t'2 (tptr (Tstruct _liteleaf noattr))) :: nil)))
      Sskip))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _iter (tptr (Tstruct _litemap_iter noattr))) :: nil)))
|}.

Definition f_litemap_ref := {|
  fn_return := (tptr (Tstruct _literef noattr));
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ref, (tptr (Tstruct _literef noattr))) :: (_t'2, tbool) ::
               (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _qsbr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _literef noattr) tulong) :: nil))
    (Sset _ref (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _ref (tptr (Tstruct _literef noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
            (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr)))
        (Etempvar _map (tptr (Tstruct _litemap noattr))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _qsbr
                (tptr (Tstruct _qsbr noattr))))
            (Scall (Some _t'2)
              (Evar _qsbr_register (Tfunction
                                     (Tcons (tptr (Tstruct _qsbr noattr))
                                       (Tcons
                                         (tptr (Tstruct _qsbr_ref noattr))
                                         Tnil)) tbool cc_default))
              ((Etempvar _t'3 (tptr (Tstruct _qsbr noattr))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
                     (Tstruct _literef noattr)) _qref
                   (Tstruct _qsbr_ref noattr))
                 (tptr (Tstruct _qsbr_ref noattr))) :: nil)))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tbool)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
              (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)))))
            Sskip))
        (Sreturn (Some (Etempvar _ref (tptr (Tstruct _literef noattr)))))))))
|}.

Definition f_litemap_unref := {|
  fn_return := (tptr (Tstruct _litemap noattr));
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_map, (tptr (Tstruct _litemap noattr))) ::
               (_t'1, (tptr (Tstruct _qsbr noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _map
    (Efield
      (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
        (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
            (Tstruct _litemap noattr)) _qsbr (tptr (Tstruct _qsbr noattr))))
      (Scall None
        (Evar _qsbr_unregister (Tfunction
                                 (Tcons (tptr (Tstruct _qsbr noattr))
                                   (Tcons (tptr (Tstruct _qsbr_ref noattr))
                                     Tnil)) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _qsbr noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
               (Tstruct _literef noattr)) _qref (Tstruct _qsbr_ref noattr))
           (tptr (Tstruct _qsbr_ref noattr))) :: nil)))
    (Ssequence
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _ref (tptr (Tstruct _literef noattr))) :: nil))
      (Sreturn (Some (Etempvar _map (tptr (Tstruct _litemap noattr))))))))
|}.

Definition f_litemap_park := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _qsbr_park (Tfunction (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil)
                     tvoid cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
         (Tstruct _literef noattr)) _qref (Tstruct _qsbr_ref noattr))
     (tptr (Tstruct _qsbr_ref noattr))) :: nil))
|}.

Definition f_litemap_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _qsbr_resume (Tfunction
                       (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil) tvoid
                       cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
         (Tstruct _literef noattr)) _qref (Tstruct _qsbr_ref noattr))
     (tptr (Tstruct _qsbr_ref noattr))) :: nil))
|}.

Definition f_litemap_refresh_qstate := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ref, (tptr (Tstruct _literef noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, (tptr (Tstruct _litehmap noattr))) ::
               (_t'3, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
            (Tstruct _literef noattr)) _map (tptr (Tstruct _litemap noattr))))
      (Scall (Some _t'1)
        (Evar _litehmap_load (Tfunction
                               (Tcons (tptr (Tstruct _litemap noattr)) Tnil)
                               (tptr (Tstruct _litehmap noattr)) cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _litemap noattr))) :: nil)))
    (Scall (Some _t'2)
      (Evar _litehmap_version_load (Tfunction
                                     (Tcons (tptr (Tstruct _litehmap noattr))
                                       Tnil) tulong cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _litehmap noattr))) :: nil)))
  (Scall None
    (Evar _qsbr_update (Tfunction
                         (Tcons (tptr (Tstruct _qsbr_ref noattr))
                           (Tcons tulong Tnil)) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _ref (tptr (Tstruct _literef noattr)))
           (Tstruct _literef noattr)) _qref (Tstruct _qsbr_ref noattr))
       (tptr (Tstruct _qsbr_ref noattr))) :: (Etempvar _t'2 tulong) :: nil)))
|}.

Definition f_litemap_clean_hmap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _x tuint)
                     (Econst_int (Int.repr 2) tint) tint)
        Sskip
        Sbreak)
      (Sassign
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _hmap2
                (tarray (Tstruct _litehmap noattr) 2)) (Etempvar _x tuint)
              (tptr (Tstruct _litehmap noattr))) (Tstruct _litehmap noattr))
          _nkeys tulong) (Econst_int (Int.repr 0) tint)))
    (Sset _x
      (Ebinop Oadd (Etempvar _x tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_litemap_free_leaf_keys := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_leaf, (tptr (Tstruct _liteleaf noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_nr, tuint) :: (_i, tuint) :: (_curr, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _kv noattr))
                          (Tcons (tptr tvoid) Tnil)) tvoid cc_default))) ::
               (_t'1, (tptr (Tstruct _kv noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _nr
    (Efield
      (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
        (Tstruct _liteleaf noattr)) _nr_keys tuint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _nr tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _curr
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
                      (Tstruct _liteleaf noattr)) _kvs
                    (tarray (tptr (Tstruct _kv noattr)) 128))
                  (Etempvar _i tuint) (tptr (tptr (Tstruct _kv noattr))))
                (tptr (Tstruct _kv noattr))))
            (Ssequence
              (Scall None
                (Evar _debug_assert (Tfunction (Tcons tbool Tnil) tvoid
                                      cc_default))
                ((Etempvar _curr (tptr tvoid)) :: nil))
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _map (tptr (Tstruct _litemap noattr)))
                        (Tstruct _litemap noattr)) _mm
                      (Tstruct _kvmap_mm noattr)) _free
                    (tptr (Tfunction
                            (Tcons (tptr (Tstruct _kv noattr))
                              (Tcons (tptr tvoid) Tnil)) tvoid cc_default))))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _map (tptr (Tstruct _litemap noattr)))
                          (Tstruct _litemap noattr)) _mm
                        (Tstruct _kvmap_mm noattr)) _priv (tptr tvoid)))
                  (Scall None
                    (Etempvar _t'2 (tptr (Tfunction
                                           (Tcons (tptr (Tstruct _kv noattr))
                                             (Tcons (tptr tvoid) Tnil)) tvoid
                                           cc_default)))
                    ((Etempvar _curr (tptr tvoid)) ::
                     (Etempvar _t'3 (tptr tvoid)) :: nil)))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            (Tstruct _liteleaf noattr)) _anchor (tptr (Tstruct _kv noattr))))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _kv noattr))) :: nil)))))
|}.

Definition f_litemap_clean_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
               (_t'1, (tptr (Tstruct _slab noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _litemap_clean_hmap (Tfunction
                                (Tcons (tptr (Tstruct _litemap noattr)) Tnil)
                                tvoid cc_default))
    ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Sset _leaf
        (Efield
          (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
            (Tstruct _litemap noattr)) _leaf0
          (tptr (Tstruct _liteleaf noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
            Sskip
            Sbreak)
          (Scall None
            (Evar _litemap_free_leaf_keys (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _litemap noattr))
                                              (Tcons
                                                (tptr (Tstruct _liteleaf noattr))
                                                Tnil)) tvoid cc_default))
            ((Etempvar _map (tptr (Tstruct _litemap noattr))) ::
             (Etempvar _leaf (tptr (Tstruct _liteleaf noattr))) :: nil)))
        (Sset _leaf
          (Efield
            (Ederef (Etempvar _leaf (tptr (Tstruct _liteleaf noattr)))
              (Tstruct _liteleaf noattr)) _next
            (tptr (Tstruct _liteleaf noattr))))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
              (Tstruct _litemap noattr)) _slab_leaf
            (tptr (Tstruct _slab noattr))))
        (Scall None
          (Evar _slab_free_all (Tfunction
                                 (Tcons (tptr (Tstruct _slab noattr)) Tnil)
                                 tvoid cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _slab noattr))) :: nil)))
      (Sassign
        (Efield
          (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
            (Tstruct _litemap noattr)) _leaf0
          (tptr (Tstruct _liteleaf noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
|}.

Definition f_litemap_clean := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _litemap_clean_helper (Tfunction
                                  (Tcons (tptr (Tstruct _litemap noattr))
                                    Tnil) tvoid cc_default))
    ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
  (Scall None
    (Evar _litemap_create_leaf0 (Tfunction
                                  (Tcons (tptr (Tstruct _litemap noattr))
                                    Tnil) tbool cc_default))
    ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil)))
|}.

Definition f_litemap_destroy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_hmap, (tptr (Tstruct _litehmap noattr))) ::
               (_t'4, (tptr (Tstruct __7144 noattr))) ::
               (_t'3, (tptr (Tstruct __7144 noattr))) ::
               (_t'2, (tptr (Tstruct _qsbr noattr))) ::
               (_t'1, (tptr (Tstruct _slab noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _litemap_clean_helper (Tfunction
                                  (Tcons (tptr (Tstruct _litemap noattr))
                                    Tnil) tvoid cc_default))
    ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 2) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _hmap
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                    (Tstruct _litemap noattr)) _hmap2
                  (tarray (Tstruct _litehmap noattr) 2)) (Etempvar _i tuint)
                (tptr (Tstruct _litehmap noattr))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                    (Tstruct _litehmap noattr)) _pairs
                  (tptr (Tstruct __7144 noattr))))
              (Sifthenelse (Etempvar _t'3 (tptr (Tstruct __7144 noattr)))
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _hmap (tptr (Tstruct _litehmap noattr)))
                        (Tstruct _litehmap noattr)) _pairs
                      (tptr (Tstruct __7144 noattr))))
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _t'4 (tptr (Tstruct __7144 noattr))) :: nil)))
                Sskip))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
              (Tstruct _litemap noattr)) _qsbr (tptr (Tstruct _qsbr noattr))))
        (Scall None
          (Evar _qsbr_destroy (Tfunction
                                (Tcons (tptr (Tstruct _qsbr noattr)) Tnil)
                                tvoid cc_default))
          ((Etempvar _t'2 (tptr (Tstruct _qsbr noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                (Tstruct _litemap noattr)) _slab_leaf
              (tptr (Tstruct _slab noattr))))
          (Scall None
            (Evar _slab_destroy (Tfunction
                                  (Tcons (tptr (Tstruct _slab noattr)) Tnil)
                                  tvoid cc_default))
            ((Etempvar _t'1 (tptr (Tstruct _slab noattr))) :: nil)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _map (tptr (Tstruct _litemap noattr))) :: nil))))))
|}.

Definition f_litemap_fprint := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_map, (tptr (Tstruct _litemap noattr))) ::
                (_out, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
              (Tstruct _litemap noattr)) _hmap2
            (tarray (Tstruct _litehmap noattr) 2))
          (Econst_int (Int.repr 0) tint) (tptr (Tstruct _litehmap noattr)))
        (Tstruct _litehmap noattr)) _nkeys tulong))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                (Tstruct _litemap noattr)) _hmap2
              (tarray (Tstruct _litehmap noattr) 2))
            (Econst_int (Int.repr 0) tint) (tptr (Tstruct _litehmap noattr)))
          (Tstruct _litehmap noattr)) _nalloc tulong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                  (Tstruct _litemap noattr)) _hmap2
                (tarray (Tstruct _litehmap noattr) 2))
              (Econst_int (Int.repr 1) tint)
              (tptr (Tstruct _litehmap noattr))) (Tstruct _litehmap noattr))
          _nkeys tulong))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _map (tptr (Tstruct _litemap noattr)))
                    (Tstruct _litemap noattr)) _hmap2
                  (tarray (Tstruct _litehmap noattr) 2))
                (Econst_int (Int.repr 1) tint)
                (tptr (Tstruct _litehmap noattr)))
              (Tstruct _litehmap noattr)) _nalloc tulong))
        (Scall None
          (Evar _fprintf (Tfunction
                           (Tcons (tptr (Tstruct __IO_FILE noattr))
                             (Tcons (tptr tschar) Tnil)) tint
                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
          ((Etempvar _out (tptr (Tstruct __IO_FILE noattr))) ::
           (Evar ___stringlit_1 (tarray tschar 22)) ::
           (Etempvar _t'1 tulong) :: (Etempvar _t'2 tulong) ::
           (Etempvar _t'3 tulong) :: (Etempvar _t'4 tulong) :: nil))))))
|}.

Definition v_kvmap_api_litemap := {|
  gvar_info := (Tstruct _kvmap_api noattr);
  gvar_init := (Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_addrof _litemap_put (Ptrofs.repr 0) ::
                Init_addrof _litemap_get (Ptrofs.repr 0) ::
                Init_addrof _litemap_probe (Ptrofs.repr 0) ::
                Init_addrof _litemap_del (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) ::
                Init_addrof _litemap_iter_create (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_seek (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_valid (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_peek (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_kref (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_kvref (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_addrof _litemap_iter_skip1 (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_skip (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_next (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_inp (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_park (Ptrofs.repr 0) ::
                Init_addrof _litemap_iter_destroy (Ptrofs.repr 0) ::
                Init_addrof _litemap_ref (Ptrofs.repr 0) ::
                Init_addrof _litemap_unref (Ptrofs.repr 0) ::
                Init_addrof _litemap_park (Ptrofs.repr 0) ::
                Init_addrof _litemap_resume (Ptrofs.repr 0) ::
                Init_addrof _litemap_clean (Ptrofs.repr 0) ::
                Init_addrof _litemap_destroy (Ptrofs.repr 0) ::
                Init_addrof _litemap_fprint (Ptrofs.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition composites : list composite_definition :=
(Composite __IO_FILE Struct
   ((__flags, tint) :: (__IO_read_ptr, (tptr tschar)) ::
    (__IO_read_end, (tptr tschar)) :: (__IO_read_base, (tptr tschar)) ::
    (__IO_write_base, (tptr tschar)) :: (__IO_write_ptr, (tptr tschar)) ::
    (__IO_write_end, (tptr tschar)) :: (__IO_buf_base, (tptr tschar)) ::
    (__IO_buf_end, (tptr tschar)) :: (__IO_save_base, (tptr tschar)) ::
    (__IO_backup_base, (tptr tschar)) :: (__IO_save_end, (tptr tschar)) ::
    (__markers, (tptr (Tstruct __IO_marker noattr))) ::
    (__chain, (tptr (Tstruct __IO_FILE noattr))) :: (__fileno, tint) ::
    (__flags2, tint) :: (__old_offset, tlong) :: (__cur_column, tushort) ::
    (__vtable_offset, tschar) :: (__shortbuf, (tarray tschar 1)) ::
    (__lock, (tptr tvoid)) :: (__offset, tlong) ::
    (__codecvt, (tptr (Tstruct __IO_codecvt noattr))) ::
    (__wide_data, (tptr (Tstruct __IO_wide_data noattr))) ::
    (__freeres_list, (tptr (Tstruct __IO_FILE noattr))) ::
    (__freeres_buf, (tptr tvoid)) :: (___pad5, tulong) :: (__mode, tint) ::
    (__unused2, (tarray tschar 20)) :: nil)
   noattr :: Composite __6333 Union ((_opaque, tuint) :: nil) noattr ::
 Composite _qsbr_ref Struct ((_opaque, (tarray tulong 3)) :: nil) noattr ::
 Composite __6648 Union ((_vlen, tuint) :: (_refcnt, tuint) :: nil) noattr ::
 Composite __6647 Struct
   ((_klen, tuint) ::
    (18727075383868559167%positive, (Tunion __6648 noattr)) :: nil)
   noattr ::
 Composite __6646 Union
   ((_kvlen, tulong) ::
    (18727075383868559167%positive, (Tstruct __6647 noattr)) :: nil)
   noattr ::
 Composite __6650 Struct ((_hashlo, tuint) :: (_hashhi, tuint) :: nil) noattr ::
 Composite __6651 Struct ((_privlo, tuint) :: (_privhi, tuint) :: nil) noattr ::
 Composite __6649 Union
   ((_hash, tulong) :: (_priv, tulong) :: (_privptr, (tptr tvoid)) ::
    (18727075383868559167%positive, (Tstruct __6650 noattr)) ::
    (19015305760020270911%positive, (Tstruct __6651 noattr)) :: nil)
   noattr ::
 Composite _kv Struct
   ((18727075383868559167%positive, (Tunion __6646 noattr)) ::
    (19015305760020270911%positive, (Tunion __6649 noattr)) ::
    (_kv, (tarray tuchar 0)) :: nil)
   noattr ::
 Composite __6653 Union ((_hash32, tuint) :: (_priv, tuint) :: nil) noattr ::
 Composite _kref Struct
   ((_len, tuint) ::
    (18727075383868559167%positive, (Tunion __6653 noattr)) ::
    (_ptr, (tptr tuchar)) :: nil)
   noattr ::
 Composite _kvref Struct
   ((_kptr, (tptr tuchar)) :: (_vptr, (tptr tuchar)) ::
    (_hdr, (Tstruct _kv noattr)) :: nil)
   noattr ::
 Composite _kvmap_mm Struct
   ((_in,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _kv noattr)) (Tcons (tptr tvoid) Tnil))
             (tptr (Tstruct _kv noattr)) cc_default))) ::
    (_out,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _kv noattr))
               (Tcons (tptr (Tstruct _kv noattr)) Tnil))
             (tptr (Tstruct _kv noattr)) cc_default))) ::
    (_free,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _kv noattr)) (Tcons (tptr tvoid) Tnil))
             tvoid cc_default))) :: (_priv, (tptr tvoid)) :: nil)
   noattr ::
 Composite _kvmap_api Struct
   ((_hashkey, tbool) :: (_ordered, tbool) :: (_threadsafe, tbool) ::
    (_readonly, tbool) :: (_irefsafe, tbool) :: (_unique, tbool) ::
    (_refpark, tbool) :: (_async, tbool) ::
    (_put,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kv noattr)) Tnil))
             tbool cc_default))) ::
    (_get,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct _kref noattr))
                 (Tcons (tptr (Tstruct _kv noattr)) Tnil)))
             (tptr (Tstruct _kv noattr)) cc_default))) ::
    (_probe,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kref noattr)) Tnil))
             tbool cc_default))) ::
    (_del,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kref noattr)) Tnil))
             tbool cc_default))) ::
    (_inpr,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct _kref noattr))
                 (Tcons
                   (tptr (Tfunction
                           (Tcons (tptr (Tstruct _kv noattr))
                             (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                   (Tcons (tptr tvoid) Tnil)))) tbool cc_default))) ::
    (_inpw,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct _kref noattr))
                 (Tcons
                   (tptr (Tfunction
                           (Tcons (tptr (Tstruct _kv noattr))
                             (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                   (Tcons (tptr tvoid) Tnil)))) tbool cc_default))) ::
    (_merge,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct _kref noattr))
                 (Tcons
                   (tptr (Tfunction
                           (Tcons (tptr (Tstruct _kv noattr))
                             (Tcons (tptr tvoid) Tnil))
                           (tptr (Tstruct _kv noattr)) cc_default))
                   (Tcons (tptr tvoid) Tnil)))) tbool cc_default))) ::
    (_delr,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct _kref noattr))
                 (Tcons (tptr (Tstruct _kref noattr)) Tnil))) tulong
             cc_default))) ::
    (_sync, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_iter_create,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))) ::
    (_iter_seek,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kref noattr)) Tnil))
             tvoid cc_default))) ::
    (_iter_valid,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tbool cc_default))) ::
    (_iter_peek,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kv noattr)) Tnil))
             (tptr (Tstruct _kv noattr)) cc_default))) ::
    (_iter_kref,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kref noattr)) Tnil))
             tbool cc_default))) ::
    (_iter_kvref,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kvref noattr)) Tnil))
             tbool cc_default))) ::
    (_iter_retain,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tulong cc_default))) ::
    (_iter_release,
     (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tulong Tnil)) tvoid
             cc_default))) ::
    (_iter_skip1,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_iter_skip,
     (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tuint Tnil)) tvoid
             cc_default))) ::
    (_iter_next,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _kv noattr)) Tnil))
             (tptr (Tstruct _kv noattr)) cc_default))) ::
    (_iter_inp,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr (Tstruct _kv noattr))
                           (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                 (Tcons (tptr tvoid) Tnil))) tbool cc_default))) ::
    (_iter_park,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_iter_destroy,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_ref,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))) ::
    (_unref,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))) ::
    (_park, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_resume, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_clean, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_destroy, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
    (_fprint,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (Tstruct __IO_FILE noattr)) Tnil)) tvoid
             cc_default))) :: nil)
   noattr ::
 Composite _liteleaf Struct
   ((_leaflock, (Tunion __6333 noattr)) :: (_padding, tuint) ::
    (_lv, tlong) :: (_prev, (tptr (Tstruct _liteleaf noattr))) ::
    (_next, (tptr (Tstruct _liteleaf noattr))) ::
    (_anchor, (tptr (Tstruct _kv noattr))) :: (_nr_keys, tuint) ::
    (_reserved, (tarray tuint 5)) ::
    (_kvs, (tarray (tptr (Tstruct _kv noattr)) 128)) :: nil)
   noattr ::
 Composite __7144 Struct
   ((_leaf, (tptr (Tstruct _liteleaf noattr))) ::
    (_anchor, (tptr (Tstruct _kv noattr))) :: nil)
   noattr ::
 Composite _litehmap Struct
   ((_hv, tlong) :: (_padding, (tarray tulong 7)) :: (_nkeys, tulong) ::
    (_nalloc, tulong) :: (_pairs, (tptr (Tstruct __7144 noattr))) ::
    (_padding1, (tarray tulong 5)) :: nil)
   noattr ::
 Composite __7145 Union
   ((_hmap_ptr, (tvolatile tlong)) ::
    (_hmap, (tptr (Tstruct _litehmap noattr))) :: nil)
   noattr ::
 Composite _litemap Struct
   ((18727075383868559167%positive, (Tunion __7145 noattr)) ::
    (_padding0, (tarray tulong 6)) ::
    (_leaf0, (tptr (Tstruct _liteleaf noattr))) ::
    (_mm, (Tstruct _kvmap_mm noattr)) ::
    (_qsbr, (tptr (Tstruct _qsbr noattr))) ::
    (_slab_leaf, (tptr (Tstruct _slab noattr))) ::
    (_padding1, (tarray tuint 4)) ::
    (_hmap2, (tarray (Tstruct _litehmap noattr) 2)) ::
    (_metalock, (Tunion __6333 noattr)) :: (_padding2, (tarray tuint 15)) ::
    nil)
   noattr ::
 Composite _litemap_iter Struct
   ((_ref, (tptr (Tstruct _literef noattr))) ::
    (_map, (tptr (Tstruct _litemap noattr))) ::
    (_leaf, (tptr (Tstruct _liteleaf noattr))) :: (_is, tuint) :: nil)
   noattr ::
 Composite _literef Struct
   ((_map, (tptr (Tstruct _litemap noattr))) ::
    (_qref, (Tstruct _qsbr_ref noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_realloc,
   Gfun(External (EF_external "realloc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memmove,
   Gfun(External (EF_external "memmove"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
     cc_default)) ::
 (_debug_assert,
   Gfun(External (EF_external "debug_assert"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tbool Tnil) tvoid cc_default)) ::
 (_yalloc,
   Gfun(External (EF_external "yalloc"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_rwlock_init,
   Gfun(External (EF_external "rwlock_init"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid cc_default)) ::
 (_rwlock_trylock_read,
   Gfun(External (EF_external "rwlock_trylock_read"
                   (mksignature (AST.Tlong :: nil) AST.Tint8unsigned
                     cc_default)) (Tcons (tptr (Tunion __6333 noattr)) Tnil)
     tbool cc_default)) ::
 (_rwlock_trylock_read_nr,
   Gfun(External (EF_external "rwlock_trylock_read_nr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     AST.Tint8unsigned cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) (Tcons tushort Tnil)) tbool
     cc_default)) ::
 (_rwlock_lock_read,
   Gfun(External (EF_external "rwlock_lock_read"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid cc_default)) ::
 (_rwlock_unlock_read,
   Gfun(External (EF_external "rwlock_unlock_read"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid cc_default)) ::
 (_rwlock_trylock_write,
   Gfun(External (EF_external "rwlock_trylock_write"
                   (mksignature (AST.Tlong :: nil) AST.Tint8unsigned
                     cc_default)) (Tcons (tptr (Tunion __6333 noattr)) Tnil)
     tbool cc_default)) ::
 (_rwlock_trylock_write_nr,
   Gfun(External (EF_external "rwlock_trylock_write_nr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     AST.Tint8unsigned cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) (Tcons tushort Tnil)) tbool
     cc_default)) ::
 (_rwlock_lock_write,
   Gfun(External (EF_external "rwlock_lock_write"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid cc_default)) ::
 (_rwlock_unlock_write,
   Gfun(External (EF_external "rwlock_unlock_write"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tunion __6333 noattr)) Tnil) tvoid cc_default)) ::
 (_slab_create,
   Gfun(External (EF_external "slab_create"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil))
     (tptr (Tstruct _slab noattr)) cc_default)) ::
 (_slab_alloc_safe,
   Gfun(External (EF_external "slab_alloc_safe"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _slab noattr)) Tnil) (tptr tvoid) cc_default)) ::
 (_slab_free_safe,
   Gfun(External (EF_external "slab_free_safe"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _slab noattr)) (Tcons (tptr tvoid) Tnil)) tvoid
     cc_default)) ::
 (_slab_free_all,
   Gfun(External (EF_external "slab_free_all"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _slab noattr)) Tnil) tvoid cc_default)) ::
 (_slab_destroy,
   Gfun(External (EF_external "slab_destroy"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _slab noattr)) Tnil) tvoid cc_default)) ::
 (_qsbr_create,
   Gfun(External (EF_external "qsbr_create"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (Tstruct _qsbr noattr)) cc_default)) ::
 (_qsbr_register,
   Gfun(External (EF_external "qsbr_register"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     AST.Tint8unsigned cc_default))
     (Tcons (tptr (Tstruct _qsbr noattr))
       (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil)) tbool cc_default)) ::
 (_qsbr_unregister,
   Gfun(External (EF_external "qsbr_unregister"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _qsbr noattr))
       (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil)) tvoid cc_default)) ::
 (_qsbr_update,
   Gfun(External (EF_external "qsbr_update"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _qsbr_ref noattr)) (Tcons tulong Tnil)) tvoid
     cc_default)) ::
 (_qsbr_park,
   Gfun(External (EF_external "qsbr_park"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil) tvoid cc_default)) ::
 (_qsbr_resume,
   Gfun(External (EF_external "qsbr_resume"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _qsbr_ref noattr)) Tnil) tvoid cc_default)) ::
 (_qsbr_wait,
   Gfun(External (EF_external "qsbr_wait"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _qsbr noattr)) (Tcons tulong Tnil)) tvoid
     cc_default)) ::
 (_qsbr_destroy,
   Gfun(External (EF_external "qsbr_destroy"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _qsbr noattr)) Tnil) tvoid cc_default)) ::
 (_kv_kref,
   Gfun(External (EF_external "kv_kref"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _kref noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) tvoid
     {|cc_vararg:=None; cc_unproto:=false; cc_structret:=true|})) ::
 (_kv_null,
   Gfun(External (EF_external "kv_null"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (Tstruct _kv noattr)) cc_default)) ::
 (_kv_dup_key,
   Gfun(External (EF_external "kv_dup_key"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _kv noattr)) Tnil) (tptr (Tstruct _kv noattr))
     cc_default)) ::
 (_kv_dup2,
   Gfun(External (EF_external "kv_dup2"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default))
     (Tcons (tptr (Tstruct _kv noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) (tptr (Tstruct _kv noattr))
     cc_default)) ::
 (_kv_compare,
   Gfun(External (EF_external "kv_compare"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _kv noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) tint cc_default)) ::
 (_kvmap_mm_dup, Gvar v_kvmap_mm_dup) ::
 (_kref_ref_kv,
   Gfun(External (EF_external "kref_ref_kv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _kref noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) tvoid cc_default)) ::
 (_kref_kv_compare,
   Gfun(External (EF_external "kref_kv_compare"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _kref noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) tint cc_default)) ::
 (_kvref_ref_kv,
   Gfun(External (EF_external "kvref_ref_kv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _kvref noattr))
       (Tcons (tptr (Tstruct _kv noattr)) Tnil)) tvoid cc_default)) ::
 (_liteleaf_alloc, Gfun(Internal f_liteleaf_alloc)) ::
 (_liteleaf_free, Gfun(Internal f_liteleaf_free)) ::
 (_liteleaf_lock_write, Gfun(Internal f_liteleaf_lock_write)) ::
 (_liteleaf_lock_read, Gfun(Internal f_liteleaf_lock_read)) ::
 (_liteleaf_unlock_write, Gfun(Internal f_liteleaf_unlock_write)) ::
 (_liteleaf_unlock_read, Gfun(Internal f_liteleaf_unlock_read)) ::
 (_litehmap_lock, Gfun(Internal f_litehmap_lock)) ::
 (_litehmap_unlock, Gfun(Internal f_litehmap_unlock)) ::
 (_litehmap_switch, Gfun(Internal f_litehmap_switch)) ::
 (_litehmap_load, Gfun(Internal f_litehmap_load)) ::
 (_litehmap_store, Gfun(Internal f_litehmap_store)) ::
 (_litehmap_version_load, Gfun(Internal f_litehmap_version_load)) ::
 (_litehmap_version_store, Gfun(Internal f_litehmap_version_store)) ::
 (_atomic_load_explicit,
   Gfun(External (EF_external "atomic_load_explicit"
                   (mksignature nil AST.Tint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_liteleaf_version_load, Gfun(Internal f_liteleaf_version_load)) ::
 (_atomic_store_explicit,
   Gfun(External (EF_external "atomic_store_explicit"
                   (mksignature nil AST.Tint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     Tnil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_liteleaf_version_store, Gfun(Internal f_liteleaf_version_store)) ::
 (_litemap_qsbr_update_pause, Gfun(Internal f_litemap_qsbr_update_pause)) ::
 (_litemap_create_leaf0, Gfun(Internal f_litemap_create_leaf0)) ::
 (_litemap_create, Gfun(Internal f_litemap_create)) ::
 (_litehmap_jump_i, Gfun(Internal f_litehmap_jump_i)) ::
 (_litemap_jump_leaf, Gfun(Internal f_litemap_jump_leaf)) ::
 (_litemap_jump_leaf_read, Gfun(Internal f_litemap_jump_leaf_read)) ::
 (_litemap_jump_leaf_write, Gfun(Internal f_litemap_jump_leaf_write)) ::
 (_liteleaf_match_i, Gfun(Internal f_liteleaf_match_i)) ::
 (_liteleaf_seek_ge, Gfun(Internal f_liteleaf_seek_ge)) ::
 (_liteleaf_update, Gfun(Internal f_liteleaf_update)) ::
 (_liteleaf_insert, Gfun(Internal f_liteleaf_insert)) ::
 (_litemap_split_leaf, Gfun(Internal f_litemap_split_leaf)) ::
 (_liteleaf_remove, Gfun(Internal f_liteleaf_remove)) ::
 (_liteleaf_merge, Gfun(Internal f_liteleaf_merge)) ::
 (_liteleaf_split_undo, Gfun(Internal f_liteleaf_split_undo)) ::
 (_litemap_get, Gfun(Internal f_litemap_get)) ::
 (_litemap_probe, Gfun(Internal f_litemap_probe)) ::
 (_litehmap_seek_ge, Gfun(Internal f_litehmap_seek_ge)) ::
 (_litemeta_split, Gfun(Internal f_litemeta_split)) ::
 (_litemap_split_meta, Gfun(Internal f_litemap_split_meta)) ::
 (_litemap_split_insert, Gfun(Internal f_litemap_split_insert)) ::
 (_litemeta_merge, Gfun(Internal f_litemeta_merge)) ::
 (_litemap_meta_merge, Gfun(Internal f_litemap_meta_merge)) ::
 (_litemap_meta_leaf_merge, Gfun(Internal f_litemap_meta_leaf_merge)) ::
 (_litemap_put, Gfun(Internal f_litemap_put)) ::
 (_litemap_del_try_merge, Gfun(Internal f_litemap_del_try_merge)) ::
 (_litemap_del, Gfun(Internal f_litemap_del)) ::
 (_litemap_iter_create, Gfun(Internal f_litemap_iter_create)) ::
 (_litemap_iter_fix, Gfun(Internal f_litemap_iter_fix)) ::
 (_litemap_iter_seek, Gfun(Internal f_litemap_iter_seek)) ::
 (_litemap_iter_valid, Gfun(Internal f_litemap_iter_valid)) ::
 (_litemap_iter_current, Gfun(Internal f_litemap_iter_current)) ::
 (_litemap_iter_peek, Gfun(Internal f_litemap_iter_peek)) ::
 (_litemap_iter_kref, Gfun(Internal f_litemap_iter_kref)) ::
 (_litemap_iter_kvref, Gfun(Internal f_litemap_iter_kvref)) ::
 (_litemap_iter_skip1, Gfun(Internal f_litemap_iter_skip1)) ::
 (_litemap_iter_skip, Gfun(Internal f_litemap_iter_skip)) ::
 (_litemap_iter_next, Gfun(Internal f_litemap_iter_next)) ::
 (_litemap_iter_inp, Gfun(Internal f_litemap_iter_inp)) ::
 (_litemap_iter_park, Gfun(Internal f_litemap_iter_park)) ::
 (_litemap_iter_destroy, Gfun(Internal f_litemap_iter_destroy)) ::
 (_litemap_ref, Gfun(Internal f_litemap_ref)) ::
 (_litemap_unref, Gfun(Internal f_litemap_unref)) ::
 (_litemap_park, Gfun(Internal f_litemap_park)) ::
 (_litemap_resume, Gfun(Internal f_litemap_resume)) ::
 (_litemap_refresh_qstate, Gfun(Internal f_litemap_refresh_qstate)) ::
 (_litemap_clean_hmap, Gfun(Internal f_litemap_clean_hmap)) ::
 (_litemap_free_leaf_keys, Gfun(Internal f_litemap_free_leaf_keys)) ::
 (_litemap_clean_helper, Gfun(Internal f_litemap_clean_helper)) ::
 (_litemap_clean, Gfun(Internal f_litemap_clean)) ::
 (_litemap_destroy, Gfun(Internal f_litemap_destroy)) ::
 (_litemap_fprint, Gfun(Internal f_litemap_fprint)) ::
 (_kvmap_api_litemap, Gvar v_kvmap_api_litemap) :: nil).

Definition public_idents : list ident :=
(_kvmap_api_litemap :: _litemap_fprint :: _litemap_destroy ::
 _litemap_clean :: _litemap_refresh_qstate :: _litemap_resume ::
 _litemap_park :: _litemap_unref :: _litemap_ref :: _litemap_iter_destroy ::
 _litemap_iter_park :: _litemap_iter_inp :: _litemap_iter_next ::
 _litemap_iter_skip :: _litemap_iter_skip1 :: _litemap_iter_kvref ::
 _litemap_iter_kref :: _litemap_iter_peek :: _litemap_iter_valid ::
 _litemap_iter_seek :: _litemap_iter_create :: _litemap_del ::
 _litemap_put :: _litemap_probe :: _litemap_get :: _litemap_create ::
 _atomic_store_explicit :: _atomic_load_explicit :: _kvref_ref_kv ::
 _kref_kv_compare :: _kref_ref_kv :: _kvmap_mm_dup :: _kv_compare ::
 _kv_dup2 :: _kv_dup_key :: _kv_null :: _kv_kref :: _qsbr_destroy ::
 _qsbr_wait :: _qsbr_resume :: _qsbr_park :: _qsbr_update ::
 _qsbr_unregister :: _qsbr_register :: _qsbr_create :: _slab_destroy ::
 _slab_free_all :: _slab_free_safe :: _slab_alloc_safe :: _slab_create ::
 _rwlock_unlock_write :: _rwlock_lock_write :: _rwlock_trylock_write_nr ::
 _rwlock_trylock_write :: _rwlock_unlock_read :: _rwlock_lock_read ::
 _rwlock_trylock_read_nr :: _rwlock_trylock_read :: _rwlock_init ::
 _yalloc :: _debug_assert :: _memset :: _memmove :: _free :: _realloc ::
 _malloc :: _fprintf :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


