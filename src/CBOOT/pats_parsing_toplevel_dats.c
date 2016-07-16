/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2016-7-15: 23h:30m
**
*/

/* include some .h files */
#ifndef _ATS_HEADER_NONE
#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"
#endif /* _ATS_HEADER_NONE */

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/option.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/matrix.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologues from statically loaded files */

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_tokbuf.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_tokbuf.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_3 ;
ats_ptr_type atslab_4 ;
} anairiats_rec_0 ;

typedef
struct {
ats_ptr_type atslab_token_loc ;
ats_ptr_type atslab_token_node ;
} anairiats_rec_1 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
} anairiats_sum_2 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_3 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_ABSTYPE_31) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_ASSUME_34) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_DATASORT_38) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_DATATYPE_39) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_DYNLOAD_41) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_EXCEPTION_44) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_EXTERN_45) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_FIXITY_49) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_FUN_52) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_IMPLEMENT_55) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_LOCAL_60) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_NONFIX_62) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SORTDEF_69) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_STACST_70) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_STADEF_71) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_STALOAD_72) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SYMELIM_74) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SYMINTR_75) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_TYPEDEF_80) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_VAL_81) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_VAR_82) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPIF_120) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPIFDEF_121) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPIFNDEF_122) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPERROR_129) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPPRERR_130) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPPRINT_131) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPASSERT_132) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPUNDEF_133) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPDEFINE_134) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_SRPINCLUDE_135) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__T_EOF_175) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__PE_DISCARD_92) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_isucc) (ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_iadd) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_isub) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_idiv) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ilt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_igt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_igte) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_size1_of_int1) (ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_add_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_mul2_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_ptr_alloc_tsz) (ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_ptr_zero_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_ref_make_elt_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, ListSubscriptException_make) () ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_alloc_tsz) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_initialize_funenv_tsz) (ats_ref_type, ats_size_type, ats_ptr_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_initialize_cloenv_tsz) (ats_ref_type, ats_size_type, ats_ref_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_split_tsz) (ats_ptr_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_takeout_tsz) (ats_ptr_type, ats_size_type, ats_size_type) ;
ATSextern_fun(anairiats_rec_0, atspre_array_ptr_takeout2_tsz) (ats_ptr_type, ats_size_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_foreach_funenv_tsz) (ats_ref_type, ats_ptr_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_iforeach_funenv_tsz) (ats_ref_type, ats_ptr_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_array2_ptr_takeout_tsz) (ats_ptr_type, ats_size_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atslib_qsort) (ats_ref_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__tnode_is_comment) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_incby1) (ats_ref_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_reset) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_get_token) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__parerr_make) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__the_parerrlst_add) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_SEMICOLON) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_EOF) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__pstar_fun) (ats_ref_type, ats_int_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_d0ecl_sta) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_d0ecl_dyn) (ats_ref_type, ats_int_type, ats_ref_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____copy_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____free_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type pskip_tokbuf_0 (ats_ref_type arg0) ;
static
ats_ptr_type pskip1_tokbuf_reset_1 (ats_ref_type arg0) ;
static
ats_void_type loop_5 (ats_ptr_type arg0) ;
static
ats_void_type list_vt_free_01499_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_void_type loop_3 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ptr_type arg3) ;
static
ats_ptr_type p_toplevel_fun_2 (ats_ref_type arg0, ats_ref_type arg1, ats_ptr_type arg2) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 1732(line=61, offs=1) -- 2727(line=121, offs=4)
*/
ATSstaticdec()
ats_ptr_type
pskip_tokbuf_0 (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_ptr_type, tmp2) ;
// ATSlocal_void (tmp3) ;

__ats_lab_pskip_tokbuf_0:
tmp1 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_get_token (arg0) ;
tmp2 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp1), atslab_token_node) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (((ats_sum_ptr_type)tmp2)->tag != 175) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)tmp2)->tag != 69) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp2)->tag != 38) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)tmp2)->tag != 31) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp2)->tag != 34) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)tmp2)->tag != 70) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)tmp2)->tag != 71) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (((ats_sum_ptr_type)tmp2)->tag != 80) { goto __ats_lab_8_0 ; }
__ats_lab_7_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp2)->tag != 39) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
if (((ats_sum_ptr_type)tmp2)->tag != 44) { goto __ats_lab_10_0 ; }
__ats_lab_9_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (((ats_sum_ptr_type)tmp2)->tag != 52) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
if (((ats_sum_ptr_type)tmp2)->tag != 81) { goto __ats_lab_12_0 ; }
__ats_lab_11_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (((ats_sum_ptr_type)tmp2)->tag != 82) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
if (((ats_sum_ptr_type)tmp2)->tag != 55) { goto __ats_lab_14_0 ; }
__ats_lab_13_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (((ats_sum_ptr_type)tmp2)->tag != 49) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
if (((ats_sum_ptr_type)tmp2)->tag != 62) { goto __ats_lab_16_0 ; }
__ats_lab_15_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (((ats_sum_ptr_type)tmp2)->tag != 75) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
if (((ats_sum_ptr_type)tmp2)->tag != 74) { goto __ats_lab_18_0 ; }
__ats_lab_17_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_18 */
__ats_lab_18_0:
if (((ats_sum_ptr_type)tmp2)->tag != 45) { goto __ats_lab_19_0 ; }
__ats_lab_18_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_19 */
__ats_lab_19_0:
if (((ats_sum_ptr_type)tmp2)->tag != 60) { goto __ats_lab_20_0 ; }
__ats_lab_19_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_20 */
__ats_lab_20_0:
if (((ats_sum_ptr_type)tmp2)->tag != 72) { goto __ats_lab_21_0 ; }
__ats_lab_20_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_21 */
__ats_lab_21_0:
if (((ats_sum_ptr_type)tmp2)->tag != 41) { goto __ats_lab_22_0 ; }
__ats_lab_21_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_22 */
__ats_lab_22_0:
if (((ats_sum_ptr_type)tmp2)->tag != 129) { goto __ats_lab_23_0 ; }
__ats_lab_22_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_23 */
__ats_lab_23_0:
if (((ats_sum_ptr_type)tmp2)->tag != 130) { goto __ats_lab_24_0 ; }
__ats_lab_23_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_24 */
__ats_lab_24_0:
if (((ats_sum_ptr_type)tmp2)->tag != 131) { goto __ats_lab_25_0 ; }
__ats_lab_24_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_25 */
__ats_lab_25_0:
if (((ats_sum_ptr_type)tmp2)->tag != 132) { goto __ats_lab_26_0 ; }
__ats_lab_25_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_26 */
__ats_lab_26_0:
if (((ats_sum_ptr_type)tmp2)->tag != 133) { goto __ats_lab_27_0 ; }
__ats_lab_26_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_27 */
__ats_lab_27_0:
if (((ats_sum_ptr_type)tmp2)->tag != 134) { goto __ats_lab_28_0 ; }
__ats_lab_27_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_28 */
__ats_lab_28_0:
if (((ats_sum_ptr_type)tmp2)->tag != 120) { goto __ats_lab_29_0 ; }
__ats_lab_28_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_29 */
__ats_lab_29_0:
if (((ats_sum_ptr_type)tmp2)->tag != 121) { goto __ats_lab_30_0 ; }
__ats_lab_29_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_30 */
__ats_lab_30_0:
if (((ats_sum_ptr_type)tmp2)->tag != 122) { goto __ats_lab_31_0 ; }
__ats_lab_30_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_31 */
__ats_lab_31_0:
if (((ats_sum_ptr_type)tmp2)->tag != 135) { goto __ats_lab_32_0 ; }
__ats_lab_31_1:
tmp0 = tmp1 ;
break ;

/* branch: __ats_lab_32 */
__ats_lab_32_0:
__ats_lab_32_1:
/* tmp3 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
arg0 = arg0 ;
goto __ats_lab_pskip_tokbuf_0 ; // tail call
break ;
} while (0) ;
return (tmp0) ;
} /* end of [pskip_tokbuf_0] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 2758(line=124, offs=1) -- 3249(line=154, offs=4)
*/
ATSstaticdec()
ats_ptr_type
pskip1_tokbuf_reset_1 (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
// ATSlocal_void (tmp6) ;
ATSlocal (ats_ptr_type, tmp7) ;
ATSlocal (ats_bool_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
// ATSlocal_void (tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
// ATSlocal_void (tmp14) ;

__ats_lab_pskip1_tokbuf_reset_1:
tmp5 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_get_token (arg0) ;
tmp7 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp5), atslab_token_node) ;
do {
/* branch: __ats_lab_33 */
__ats_lab_33_0:
if (((ats_sum_ptr_type)tmp7)->tag != 175) { goto __ats_lab_34_0 ; }
__ats_lab_33_1:
break ;

/* branch: __ats_lab_34 */
__ats_lab_34_0:
__ats_lab_34_1:
tmp8 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__tnode_is_comment (tmp7) ;
if (!tmp8) { goto __ats_lab_35_1 ; }
break ;

/* branch: __ats_lab_35 */
__ats_lab_35_0:
__ats_lab_35_1:
tmp9 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp5), atslab_token_loc) ;
tmp11 = (ats_sum_ptr_type)(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__PE_DISCARD_92) ;
tmp10 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__parerr_make (tmp9, tmp11) ;
/* tmp6 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__the_parerrlst_add (tmp10) ;
break ;
} while (0) ;
/* tmp12 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp13 = pskip_tokbuf_0 (arg0) ;
/* tmp14 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_reset (arg0) ;
tmp4 = tmp13 ;
return (tmp4) ;
} /* end of [pskip1_tokbuf_reset_1] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4893(line=177, offs=7) -- 5015(line=178, offs=73)
*/
ATSstaticdec()
ats_void_type
loop_5 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;

__ats_lab_loop_5:
do {
/* branch: __ats_lab_42 */
__ats_lab_42_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_43_0 ; }
__ats_lab_42_1:
tmp31 = ats_caselptrlab_mac(anairiats_sum_3, arg0, atslab_1) ;
ATS_FREE(arg0) ;
arg0 = tmp31 ;
goto __ats_lab_loop_5 ; // tail call
break ;

/* branch: __ats_lab_43 */
__ats_lab_43_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_43_1:
break ;
} while (0) ;
return /* (tmp30) */ ;
} /* end of [loop_5] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4875(line=176, offs=14) -- 5054(line=182, offs=4)
*/
ATSstaticdec()
ats_void_type
list_vt_free_01499_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp29) ;

__ats_lab_list_vt_free_01499_ats_ptr_type:
/* tmp29 = */ loop_5 (arg0) ;
return /* (tmp29) */ ;
} /* end of [list_vt_free_01499_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 3405(line=164, offs=7) -- 4619(line=209, offs=7)
*/
ATSstaticdec()
ats_void_type
loop_3 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ptr_type arg3) {
/* local vardec */
// ATSlocal_void (tmp16) ;
ATSlocal (ats_int_type, tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;
ATSlocal (ats_bool_type, tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;
// ATSlocal_void (tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
// ATSlocal_void (tmp28) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;

__ats_lab_loop_3:
tmp17 = ats_ptrget_mac(ats_int_type, arg2) ;
tmp18 = ((ats_ptr_type(*)(ats_ref_type, ats_int_type, ats_ref_type))arg3) (arg0, 1, arg2) ;
do {
/* branch: __ats_lab_36 */
__ats_lab_36_0:
__ats_lab_36_1:
tmp19 = atspre_gt_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp17) ;
if (!tmp19) { goto __ats_lab_41_1 ; }
tmp20 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_get_token (arg0) ;
tmp22 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp20), atslab_token_node) ;
do {
/* branch: __ats_lab_37 */
__ats_lab_37_0:
if (((ats_sum_ptr_type)tmp22)->tag != 175) { goto __ats_lab_38_0 ; }
__ats_lab_37_1:
ats_ptrget_mac(ats_int_type, arg2) = tmp17 ;
break ;

/* branch: __ats_lab_38 */
__ats_lab_38_0:
__ats_lab_38_1:
break ;
} while (0) ;
tmp23 = pskip1_tokbuf_reset_1 (arg0) ;
tmp24 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp23), atslab_token_node) ;
do {
/* branch: __ats_lab_39 */
__ats_lab_39_0:
if (((ats_sum_ptr_type)tmp24)->tag != 175) { goto __ats_lab_40_0 ; }
__ats_lab_39_1:
tmp25 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, arg1) = tmp25 ;
break ;

/* branch: __ats_lab_40 */
__ats_lab_40_0:
__ats_lab_40_1:
arg0 = arg0 ;
arg1 = arg1 ;
arg2 = arg2 ;
arg3 = arg3 ;
goto __ats_lab_loop_3 ; // tail call
break ;
} while (0) ;
break ;

/* branch: __ats_lab_41 */
__ats_lab_41_0:
__ats_lab_41_1:
/* tmp26 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__tokbuf_reset (arg0) ;
tmp27 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__pstar_fun (arg0, 1, &_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_SEMICOLON) ;
/* tmp28 = */ list_vt_free_01499_ats_ptr_type (tmp27) ;
tmp32 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp32, atslab_0, tmp18) ;
ats_ptrget_mac(ats_ptr_type, arg1) = tmp32 ;
// if (ats_ptrget_mac(ats_ptr_type, arg1) == (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
tmp33 = &ats_caselptrlab_mac(anairiats_sum_3, ats_ptrget_mac(ats_ptr_type, arg1), atslab_1) ;
arg0 = arg0 ;
arg1 = tmp33 ;
arg2 = arg2 ;
arg3 = arg3 ;
goto __ats_lab_loop_3 ; // tail call
break ;
} while (0) ;
return /* (tmp16) */ ;
} /* end of [loop_3] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 3308(line=159, offs=1) -- 4822(line=218, offs=4)
*/
ATSstaticdec()
ats_ptr_type
p_toplevel_fun_2 (ats_ref_type arg0, ats_ref_type arg1, ats_ptr_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp34) ;
// ATSlocal_void (tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;

__ats_lab_p_toplevel_fun_2:
ats_ptrget_mac(ats_int_type, arg1) = 0 ;
/* ats_ptr_type tmp34 ; */
/* tmp35 = */ loop_3 (arg0, (&tmp34), arg1, arg2) ;
tmp36 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_EOF (arg0, 0, arg1) ;
tmp15 = ats_castfn_mac(ats_ptr_type, tmp34) ;
return (tmp15) ;
} /* end of [p_toplevel_fun_2] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 4897(line=223, offs=16) -- 4950(line=223, offs=69)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_sta (ats_ref_type arg0, ats_ref_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp37) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_sta:
tmp37 = p_toplevel_fun_2 (arg0, arg1, &_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_d0ecl_sta) ;
return (tmp37) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_sta] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_parsing_toplevel.dats: 4976(line=225, offs=16) -- 5029(line=225, offs=69)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_dyn (ats_ref_type arg0, ats_ref_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp38) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_dyn:
tmp38 = p_toplevel_fun_2 (arg0, arg1, &_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_d0ecl_dyn) ;
return (tmp38) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__p_toplevel_dyn] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__staload_flag = 1 ;

// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_tokbuf_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_parsing_toplevel_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e12_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____copy_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____free_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_parsing_toplevel_dats.c] */
