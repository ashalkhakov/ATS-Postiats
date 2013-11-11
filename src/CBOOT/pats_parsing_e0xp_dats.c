/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-11-10: 21h:24m
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
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/string.cats"
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
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_2 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_3 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_vt_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_IF_53) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_IDENT_alp_129) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_CHAR_136) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_INTEGER_137) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_FLOAT_138) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_STRING_140) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_LPAREN_141) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__T_PERCENTLPAREN_158) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atme0xp_59) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
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
ATSextern_fun(ats_uint_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_ntok) (ats_ref_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_token) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_i0nt) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_c0har) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_f0loat) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_s0tring) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_i0de) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_list) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_app) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_eval) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_if) (ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_make_stringid) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__datsdef_make) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__tokbuf_set_ntok_null) (ats_ref_type, ats_uint_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_THEN) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__is_ELSE) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_RPAREN) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__is_EQ) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptokentopt_fun) (ats_ref_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pstar_fun0_COMMA) (ats_ref_type, ats_int_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pstar1_fun) (ats_ref_type, ats_int_type, ats_ref_type, ats_ptr_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptest_fun) (ats_ref_type, ats_ptr_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pif_fun) (ats_ref_type, ats_int_type, ats_ref_type, ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptokwrap_fun) (ats_ref_type, ats_int_type, ats_ref_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_i0de) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp) (ats_ref_type, ats_int_type, ats_ref_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____copy_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____free_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type p_e0xpseq_vt_0 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) ;
static
ats_void_type loop_3 (ats_ptr_type arg0) ;
static
ats_void_type list_vt_free_01498_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_ptr_type p_atme0xp_tok_1 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2, ats_ptr_type arg3) ;
static
ats_ptr_type p_atme0xp_4 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) ;
static
ats_ptr_type loop_6 (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type p_e0xp0_5 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) ;
static
ats_void_type option_vt_free_01543_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_ptr_type p_datsval_9 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 1760(line=61, offs=1) -- 1876(line=66, offs=44)
*/
ATSstaticdec()
ats_ptr_type
p_e0xpseq_vt_0 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;

__ats_lab_p_e0xpseq_vt_0:
tmp0 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pstar_fun0_COMMA (arg0, arg1, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp) ;
return (tmp0) ;
} /* end of [p_e0xpseq_vt_0] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 4893(line=177, offs=7) -- 5015(line=178, offs=73)
*/
ATSstaticdec()
ats_void_type
loop_3 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;

__ats_lab_loop_3:
do {
/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp18 = ats_caselptrlab_mac(anairiats_sum_2, arg0, atslab_1) ;
ATS_FREE(arg0) ;
arg0 = tmp18 ;
goto __ats_lab_loop_3 ; // tail call
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_7_1:
break ;
} while (0) ;
return /* (tmp17) */ ;
} /* end of [loop_3] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 4875(line=176, offs=14) -- 5054(line=182, offs=4)
*/
ATSstaticdec()
ats_void_type
list_vt_free_01498_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp16) ;

__ats_lab_list_vt_free_01498_ats_ptr_type:
/* tmp16 = */ loop_3 (arg0) ;
return /* (tmp16) */ ;
} /* end of [list_vt_free_01498_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 2097(line=83, offs=1) -- 3396(line=138, offs=4)
*/
ATSstaticdec()
ats_ptr_type
p_atme0xp_tok_1 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2, ats_ptr_type arg3) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_int_type, tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_bool_type, tmp6) ;
// ATSlocal_void (tmp7) ;
// ATSlocal_void (tmp8) ;
// ATSlocal_void (tmp9) ;
// ATSlocal_void (tmp10) ;
// ATSlocal_void (tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_bool_type, tmp14) ;
// ATSlocal_void (tmp15) ;
// ATSlocal_void (tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_bool_type, tmp22) ;
ATSlocal (ats_int_type, tmp23) ;

__ats_lab_p_atme0xp_tok_1:
tmp2 = ats_ptrget_mac(ats_int_type, arg2) ;
tmp3 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, arg3), atslab_token_loc) ;
/* ats_ptr_type tmp4 ; */
tmp5 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, arg3), atslab_token_node) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
__ats_lab_0_1:
tmp6 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptest_fun (arg0, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_i0de, (&tmp4)) ;
if (!tmp6) { goto __ats_lab_1_0 ; }
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_i0de (ats_castfn_mac(ats_ptr_type, tmp4)) ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)tmp5)->tag != 137) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
/* tmp7 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_i0nt (arg3) ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp5)->tag != 136) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
/* tmp8 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_c0har (arg3) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)tmp5)->tag != 138) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
/* tmp9 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_f0loat (arg3) ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp5)->tag != 140) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
/* tmp10 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_s0tring (arg3) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)tmp5)->tag != 141) { goto __ats_lab_8_0 ; }
__ats_lab_5_1:
/* tmp11 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp12 = p_e0xpseq_vt_0 (arg0, 0, arg2) ;
tmp13 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_RPAREN (arg0, 0, arg2) ;
tmp14 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp2) ;
if (tmp14) {
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_list (arg3, ats_castfn_mac(ats_ptr_type, tmp12), tmp13) ;
} else {
/* tmp15 = */ list_vt_free_01498_ats_ptr_type (tmp12) ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null () ;
} /* end of [if] */
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp5)->tag != 158) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
/* tmp19 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp20 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp (arg0, 0, arg2) ;
tmp21 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pif_fun (arg0, 0, arg2, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_RPAREN, tmp2) ;
tmp22 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp2) ;
if (tmp22) {
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_eval (arg3, tmp20, tmp21) ;
} else {
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null () ;
} /* end of [if] */
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
__ats_lab_9_1:
tmp23 = atspre_add_int_int (ats_ptrget_mac(ats_int_type, arg2), 1) ;
ats_ptrget_mac(ats_int_type, arg2) = tmp23 ;
tmp1 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null () ;
break ;
} while (0) ;
return (tmp1) ;
} /* end of [p_atme0xp_tok_1] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 3428(line=141, offs=1) -- 3542(line=144, offs=57)
*/
ATSstaticdec()
ats_ptr_type
p_atme0xp_4 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;

__ats_lab_p_atme0xp_4:
tmp25 = (ats_sum_ptr_type)(&_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atme0xp_59) ;
tmp24 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptokwrap_fun (arg0, arg1, arg2, &p_atme0xp_tok_1, tmp25) ;
return (tmp24) ;
} /* end of [p_atme0xp_4] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 3732(line=157, offs=7) -- 3955(line=164, offs=28)
*/
ATSstaticdec()
ats_ptr_type
loop_6 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;

__ats_lab_loop_6:
do {
/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_2, arg1, atslab_0) ;
tmp30 = ats_caselptrlab_mac(anairiats_sum_2, arg1, atslab_1) ;
ATS_FREE(arg1) ;
tmp31 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_app (arg0, tmp29) ;
arg0 = tmp31 ;
arg1 = tmp30 ;
goto __ats_lab_loop_6 ; // tail call
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
// if (arg1 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_11_1:
tmp28 = arg0 ;
break ;
} while (0) ;
return (tmp28) ;
} /* end of [loop_6] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 3618(line=153, offs=1) -- 4096(line=172, offs=4)
*/
ATSstaticdec()
ats_ptr_type
p_e0xp0_5 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;

__ats_lab_p_e0xp0_5:
tmp27 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pstar1_fun (arg0, arg1, arg2, &p_atme0xp_4) ;
do {
/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (tmp27 == (ats_sum_ptr_type)0) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp32 = ats_caselptrlab_mac(anairiats_sum_2, tmp27, atslab_0) ;
tmp33 = ats_caselptrlab_mac(anairiats_sum_2, tmp27, atslab_1) ;
ATS_FREE(tmp27) ;
tmp26 = loop_6 (tmp32, tmp33) ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
// if (tmp27 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_13_1:
tmp26 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null () ;
break ;
} while (0) ;
return (tmp26) ;
} /* end of [p_e0xp0_5] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/option_vt.dats: 2556(line=86, offs=16) -- 2611(line=87, offs=49)
*/
ATSstaticdec()
ats_void_type
option_vt_free_01543_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp51) ;

__ats_lab_option_vt_free_01543_ats_ptr_type:
do {
/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
ATS_FREE(arg0) ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_17_1:
break ;
} while (0) ;
return /* (tmp51) */ ;
} /* end of [option_vt_free_01543_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 4217(line=180, offs=8) -- 5206(line=216, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_int_type, tmp35) ;
ATSlocal (ats_uint_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
ATSlocal (ats_bool_type, tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_bool_type, tmp43) ;
// ATSlocal_void (tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_bool_type, tmp49) ;
// ATSlocal_void (tmp50) ;
ATSlocal (ats_int_type, tmp52) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp:
tmp35 = ats_ptrget_mac(ats_int_type, arg2) ;
tmp36 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_ntok (arg0) ;
tmp37 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_token (arg0) ;
/* ats_ptr_type tmp38 ; */
tmp39 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp37), atslab_token_node) ;
do {
/* branch: __ats_lab_14 */
__ats_lab_14_0:
__ats_lab_14_1:
tmp40 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptest_fun (arg0, &p_e0xp0_5, (&tmp38)) ;
if (!tmp40) { goto __ats_lab_15_0 ; }
tmp41 = ats_castfn_mac(ats_ptr_type, tmp38) ;
tmp42 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp (arg0, 0, arg2) ;
tmp43 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp35) ;
if (tmp43) {
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_app (tmp41, tmp42) ;
} else {
ats_ptrget_mac(ats_int_type, arg2) = tmp35 ;
tmp34 = tmp41 ;
} /* end of [if] */
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
if (((ats_sum_ptr_type)tmp39)->tag != 53) { goto __ats_lab_18_0 ; }
__ats_lab_15_1:
/* tmp44 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp45 = p_e0xp0_5 (arg0, arg1, arg2) ;
tmp46 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pif_fun (arg0, arg1, arg2, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_THEN, tmp35) ;
tmp47 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__pif_fun (arg0, arg1, arg2, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp, tmp35) ;
tmp48 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptokentopt_fun (arg0, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__is_ELSE, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp) ;
tmp49 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp35) ;
if (tmp49) {
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_if (tmp37, tmp45, tmp47, ats_castfn_mac(ats_ptr_type, tmp48)) ;
} else {
/* tmp50 = */ option_vt_free_01543_ats_ptr_type (tmp48) ;
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__tokbuf_set_ntok_null (arg0, tmp36) ;
} /* end of [if] */
break ;

/* branch: __ats_lab_18 */
__ats_lab_18_0:
__ats_lab_18_1:
tmp52 = atspre_add_int_int (ats_ptrget_mac(ats_int_type, arg2), 1) ;
ats_ptrget_mac(ats_int_type, arg2) = tmp52 ;
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__synent_null () ;
break ;
} while (0) ;
return (tmp34) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_e0xp] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 5340(line=226, offs=1) -- 6032(line=255, offs=4)
*/
ATSstaticdec()
ats_ptr_type
p_datsval_9 (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp53) ;
ATSlocal (ats_uint_type, tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
ATSlocal (ats_ptr_type, tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
// ATSlocal_void (tmp60) ;
// ATSlocal_void (tmp61) ;
// ATSlocal_void (tmp62) ;
// ATSlocal_void (tmp63) ;
// ATSlocal_void (tmp64) ;

__ats_lab_p_datsval_9:
tmp54 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_ntok (arg0) ;
tmp55 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_token (arg0) ;
tmp56 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp55), atslab_token_loc) ;
/* ats_ptr_type tmp57 ; */
tmp58 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp55), atslab_token_node) ;
do {
/* branch: __ats_lab_19 */
__ats_lab_19_0:
if (((ats_sum_ptr_type)tmp58)->tag != 129) { goto __ats_lab_20_0 ; }
__ats_lab_19_1:
tmp59 = ats_caselptrlab_mac(anairiats_sum_3, tmp58, atslab_0) ;
/* tmp60 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_make_stringid (tmp56, tmp59) ;
break ;

/* branch: __ats_lab_20 */
__ats_lab_20_0:
if (((ats_sum_ptr_type)tmp58)->tag != 137) { goto __ats_lab_21_0 ; }
__ats_lab_20_1:
/* tmp61 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_i0nt (tmp55) ;
break ;

/* branch: __ats_lab_21 */
__ats_lab_21_0:
if (((ats_sum_ptr_type)tmp58)->tag != 136) { goto __ats_lab_22_0 ; }
__ats_lab_21_1:
/* tmp62 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_c0har (tmp55) ;
break ;

/* branch: __ats_lab_22 */
__ats_lab_22_0:
if (((ats_sum_ptr_type)tmp58)->tag != 138) { goto __ats_lab_23_0 ; }
__ats_lab_22_1:
/* tmp63 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_f0loat (tmp55) ;
break ;

/* branch: __ats_lab_23 */
__ats_lab_23_0:
if (((ats_sum_ptr_type)tmp58)->tag != 140) { goto __ats_lab_24_0 ; }
__ats_lab_23_1:
/* tmp64 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_incby1 (arg0) ;
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_s0tring (tmp55) ;
break ;

/* branch: __ats_lab_24 */
__ats_lab_24_0:
__ats_lab_24_1:
tmp53 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__e0xp_make_stringid (tmp56, ATSstrcst("")) ;
break ;
} while (0) ;
return (tmp53) ;
} /* end of [p_datsval_9] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing_e0xp.dats: 6146(line=263, offs=3) -- 6541(line=278, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_datsdef (ats_ref_type arg0, ats_int_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp65) ;
ATSlocal (ats_int_type, tmp66) ;
ATSlocal (ats_uint_type, tmp67) ;
ATSlocal (ats_ptr_type, tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;
ATSlocal (ats_bool_type, tmp70) ;
ATSlocal (ats_bool_type, tmp71) ;
// ATSlocal_void (tmp72) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_datsdef:
tmp66 = ats_ptrget_mac(ats_int_type, arg2) ;
tmp67 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_get_ntok (arg0) ;
tmp68 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_i0de (arg0, arg1, arg2) ;
tmp70 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp66) ;
if (tmp70) {
tmp69 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__ptokentopt_fun (arg0, &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__is_EQ, &p_datsval_9) ;
} else {
tmp69 = (ats_sum_ptr_type)0 ;
} /* end of [if] */
tmp71 = atspre_eq_int_int (ats_ptrget_mac(ats_int_type, arg2), tmp66) ;
if (tmp71) {
tmp65 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__datsdef_make (tmp68, ats_castfn_mac(ats_ptr_type, tmp69)) ;
} else {
/* tmp72 = */ option_vt_free_01543_ats_ptr_type (tmp69) ;
tmp65 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__tokbuf_set_ntok_null (arg0, tmp67) ;
} /* end of [if] */
return (tmp65) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_datsdef] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__staload_flag = 1 ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_e0xp_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e11_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____copy_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____free_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_parsing_e0xp_dats.c] */
