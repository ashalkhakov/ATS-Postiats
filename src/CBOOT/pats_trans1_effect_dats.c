/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-10-23: 13h:36m
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

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

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

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_e0fftag_loc ;
ats_ptr_type atslab_e0fftag_node ;
} anairiats_rec_0 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_1 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_2 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
} anairiats_sum_3 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_4 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_int_type atslab_1 ;
} anairiats_sum_5 ;

typedef struct {
ats_ptr_type atslab_0 ;
} anairiats_sum_6 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_int_type atslab_1 ;
ats_int_type atslab_2 ;
} anairiats_sum_7 ;

typedef struct {
ats_int_type atslab_0 ;
} anairiats_sum_8 ;

typedef
struct {
ats_ptr_type atslab_0 ;
ats_int_type atslab_1 ;
ats_int_type atslab_2 ;
ats_ptr_type atslab_3 ;
} anairiats_rec_9 ;

typedef struct {
int tag ;
ats_uint_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_10 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__FUNCLOfun_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__FUNCLOclo_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGint_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGcst_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGvar_2) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGprf_3) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGlin_4) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGfun_5) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__E0FFTAGclo_6) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__EFFCSTall_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__EFFCSTnil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__EFFCSTset_2) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_prerr_newline) () ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_string_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_prerr_string) (ats_ptr_type) ;
ATSextern_fun(ats_varet_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort) () ;
ATSextern_val(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ntm) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__eq_effset_effset) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add) (ats_uint_type, ats_int_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del) (ats_uint_type, ats_int_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__prerr_location) (ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_bool_type name_is_nil_0 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_all_1 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_ntm_2 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exn_3 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_ref_4 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_wrt_5 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnref_6 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnwrt_7 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnrefwrt_8 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_refwrt_9 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_lazy_10 (ats_ptr_type arg0) ;
static
ats_void_type loop_err_11 (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_void_type loop_12 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ref_type arg3, ats_ref_type arg4, ats_ptr_type arg5) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp17) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 1643(line=51, offs=4) -- 1721(line=52, offs=44)
*/
ATSstaticdec()
ats_bool_type
name_is_nil_0 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp0) ;
ATSlocal (ats_bool_type, tmp1) ;

__ats_lab_name_is_nil_0:
tmp1 = atspre_eq_string_string (arg0, ATSstrcst("0")) ;
if (tmp1) {
tmp0 = ats_true_bool ;
} else {
tmp0 = atspre_eq_string_string (arg0, ATSstrcst("nil")) ;
} /* end of [if] */
return (tmp0) ;
} /* end of [name_is_nil_0] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 1725(line=53, offs=4) -- 1803(line=54, offs=44)
*/
ATSstaticdec()
ats_bool_type
name_is_all_1 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp2) ;
ATSlocal (ats_bool_type, tmp3) ;

__ats_lab_name_is_all_1:
tmp3 = atspre_eq_string_string (arg0, ATSstrcst("1")) ;
if (tmp3) {
tmp2 = ats_true_bool ;
} else {
tmp2 = atspre_eq_string_string (arg0, ATSstrcst("all")) ;
} /* end of [if] */
return (tmp2) ;
} /* end of [name_is_all_1] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 1808(line=56, offs=4) -- 1892(line=57, offs=50)
*/
ATSstaticdec()
ats_bool_type
name_is_ntm_2 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp4) ;
ATSlocal (ats_bool_type, tmp5) ;

__ats_lab_name_is_ntm_2:
tmp5 = atspre_eq_string_string (arg0, ATSstrcst("ntm")) ;
if (tmp5) {
tmp4 = ats_true_bool ;
} else {
tmp4 = atspre_eq_string_string (arg0, ATSstrcst("nonterm")) ;
} /* end of [if] */
return (tmp4) ;
} /* end of [name_is_ntm_2] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 1897(line=59, offs=4) -- 1983(line=60, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_exn_3 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp6) ;
ATSlocal (ats_bool_type, tmp7) ;

__ats_lab_name_is_exn_3:
tmp7 = atspre_eq_string_string (arg0, ATSstrcst("exn")) ;
if (tmp7) {
tmp6 = ats_true_bool ;
} else {
tmp6 = atspre_eq_string_string (arg0, ATSstrcst("exception")) ;
} /* end of [if] */
return (tmp6) ;
} /* end of [name_is_exn_3] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 1987(line=61, offs=4) -- 2072(line=62, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_ref_4 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp8) ;
ATSlocal (ats_bool_type, tmp9) ;

__ats_lab_name_is_ref_4:
tmp9 = atspre_eq_string_string (arg0, ATSstrcst("ref")) ;
if (tmp9) {
tmp8 = ats_true_bool ;
} else {
tmp8 = atspre_eq_string_string (arg0, ATSstrcst("reference")) ;
} /* end of [if] */
return (tmp8) ;
} /* end of [name_is_ref_4] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2076(line=63, offs=4) -- 2158(line=64, offs=48)
*/
ATSstaticdec()
ats_bool_type
name_is_wrt_5 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp10) ;
ATSlocal (ats_bool_type, tmp11) ;

__ats_lab_name_is_wrt_5:
tmp11 = atspre_eq_string_string (arg0, ATSstrcst("wrt")) ;
if (tmp11) {
tmp10 = ats_true_bool ;
} else {
tmp10 = atspre_eq_string_string (arg0, ATSstrcst("write")) ;
} /* end of [if] */
return (tmp10) ;
} /* end of [name_is_wrt_5] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2163(line=66, offs=4) -- 2216(line=66, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_exnref_6 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp12) ;

__ats_lab_name_is_exnref_6:
tmp12 = atspre_eq_string_string (arg0, ATSstrcst("exnref")) ;
return (tmp12) ;
} /* end of [name_is_exnref_6] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2220(line=67, offs=4) -- 2273(line=67, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_exnwrt_7 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp13) ;

__ats_lab_name_is_exnwrt_7:
tmp13 = atspre_eq_string_string (arg0, ATSstrcst("exnwrt")) ;
return (tmp13) ;
} /* end of [name_is_exnwrt_7] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2277(line=68, offs=4) -- 2336(line=68, offs=63)
*/
ATSstaticdec()
ats_bool_type
name_is_exnrefwrt_8 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp14) ;

__ats_lab_name_is_exnrefwrt_8:
tmp14 = atspre_eq_string_string (arg0, ATSstrcst("exnrefwrt")) ;
return (tmp14) ;
} /* end of [name_is_exnrefwrt_8] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2340(line=69, offs=4) -- 2393(line=69, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_refwrt_9 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp15) ;

__ats_lab_name_is_refwrt_9:
tmp15 = atspre_eq_string_string (arg0, ATSstrcst("refwrt")) ;
return (tmp15) ;
} /* end of [name_is_refwrt_9] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2425(line=74, offs=4) -- 2473(line=74, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_lazy_10 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp16) ;

__ats_lab_name_is_lazy_10:
tmp16 = atspre_eq_string_string (arg0, ATSstrcst("laz")) ;
return (tmp16) ;
} /* end of [name_is_lazy_10] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2569(line=84, offs=4) -- 2867(line=95, offs=2)
*/
ATSstaticdec()
ats_void_type
loop_err_11 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;
// ATSlocal_void (tmp20) ;
// ATSlocal_void (tmp21) ;
// ATSlocal_void (tmp22) ;
// ATSlocal_void (tmp23) ;
// ATSlocal_void (tmp24) ;
// ATSlocal_void (tmp25) ;

__ats_lab_loop_err_11:
tmp19 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_e0fftag_loc) ;
/* tmp20 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__prerr_location (tmp19) ;
/* tmp21 = */ atspre_prerr_string (ATSstrcst(": error(1)")) ;
/* tmp22 = */ atspre_prerr_string (ATSstrcst(": unrecognized effect constant: [")) ;
/* tmp23 = */ atspre_prerr_string (arg1) ;
/* tmp24 = */ atspre_prerr_string (ATSstrcst("]")) ;
/* tmp25 = */ atspre_prerr_newline () ;
/* tmp18 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort () ;
return /* (tmp18) */ ;
} /* end of [loop_err_11] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 2894(line=97, offs=5) -- 7373(line=219, offs=4)
*/
ATSstaticdec()
ats_void_type
loop_12 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ref_type arg3, ats_ref_type arg4, ats_ptr_type arg5) {
/* local vardec */
// ATSlocal_void (tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
// ATSlocal_void (tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_int_type, tmp33) ;
ATSlocal (ats_bool_type, tmp35) ;
ATSlocal (ats_bool_type, tmp36) ;
ATSlocal (ats_int_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_bool_type, tmp39) ;
ATSlocal (ats_bool_type, tmp40) ;
ATSlocal (ats_int_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_bool_type, tmp43) ;
ATSlocal (ats_bool_type, tmp44) ;
ATSlocal (ats_int_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_bool_type, tmp47) ;
ATSlocal (ats_bool_type, tmp49) ;
ATSlocal (ats_uint_type, tmp50) ;
ATSlocal (ats_bool_type, tmp51) ;
ATSlocal (ats_uint_type, tmp52) ;
ATSlocal (ats_int_type, tmp53) ;
ATSlocal (ats_ptr_type, tmp54) ;
ATSlocal (ats_bool_type, tmp55) ;
ATSlocal (ats_bool_type, tmp57) ;
ATSlocal (ats_uint_type, tmp58) ;
ATSlocal (ats_bool_type, tmp59) ;
ATSlocal (ats_uint_type, tmp60) ;
ATSlocal (ats_bool_type, tmp61) ;
ATSlocal (ats_bool_type, tmp63) ;
ATSlocal (ats_uint_type, tmp64) ;
ATSlocal (ats_bool_type, tmp65) ;
ATSlocal (ats_uint_type, tmp66) ;
ATSlocal (ats_bool_type, tmp67) ;
ATSlocal (ats_bool_type, tmp69) ;
ATSlocal (ats_uint_type, tmp70) ;
ATSlocal (ats_bool_type, tmp71) ;
ATSlocal (ats_uint_type, tmp72) ;
ATSlocal (ats_bool_type, tmp73) ;
ATSlocal (ats_bool_type, tmp75) ;
ATSlocal (ats_uint_type, tmp76) ;
ATSlocal (ats_bool_type, tmp77) ;
ATSlocal (ats_uint_type, tmp78) ;
ATSlocal (ats_bool_type, tmp79) ;
ATSlocal (ats_bool_type, tmp81) ;
ATSlocal (ats_uint_type, tmp82) ;
ATSlocal (ats_uint_type, tmp83) ;
ATSlocal (ats_bool_type, tmp84) ;
ATSlocal (ats_uint_type, tmp85) ;
ATSlocal (ats_uint_type, tmp86) ;
ATSlocal (ats_bool_type, tmp87) ;
ATSlocal (ats_bool_type, tmp89) ;
ATSlocal (ats_uint_type, tmp90) ;
ATSlocal (ats_uint_type, tmp91) ;
ATSlocal (ats_bool_type, tmp92) ;
ATSlocal (ats_uint_type, tmp93) ;
ATSlocal (ats_uint_type, tmp94) ;
ATSlocal (ats_bool_type, tmp95) ;
ATSlocal (ats_bool_type, tmp97) ;
ATSlocal (ats_uint_type, tmp98) ;
ATSlocal (ats_uint_type, tmp99) ;
ATSlocal (ats_uint_type, tmp100) ;
ATSlocal (ats_bool_type, tmp101) ;
ATSlocal (ats_uint_type, tmp102) ;
ATSlocal (ats_uint_type, tmp103) ;
ATSlocal (ats_uint_type, tmp104) ;
ATSlocal (ats_bool_type, tmp105) ;
ATSlocal (ats_bool_type, tmp107) ;
ATSlocal (ats_uint_type, tmp108) ;
ATSlocal (ats_uint_type, tmp109) ;
ATSlocal (ats_bool_type, tmp110) ;
ATSlocal (ats_uint_type, tmp111) ;
ATSlocal (ats_uint_type, tmp112) ;
ATSlocal (ats_int_type, tmp113) ;
ATSlocal (ats_bool_type, tmp114) ;
ATSlocal (ats_int_type, tmp115) ;
ATSlocal (ats_int_type, tmp116) ;
ATSlocal (ats_bool_type, tmp118) ;
ATSlocal (ats_ptr_type, tmp119) ;
ATSlocal (ats_ptr_type, tmp120) ;
ATSlocal (ats_bool_type, tmp121) ;
ATSlocal (ats_int_type, tmp122) ;
ATSlocal (ats_int_type, tmp123) ;
ATSlocal (ats_int_type, tmp124) ;
ATSlocal (ats_bool_type, tmp126) ;
ATSlocal (ats_ptr_type, tmp127) ;
ATSlocal (ats_ptr_type, tmp128) ;
ATSlocal (ats_bool_type, tmp129) ;

__ats_lab_loop_12:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (arg5 == (ats_sum_ptr_type)0) { goto __ats_lab_20_0 ; }
__ats_lab_0_1:
tmp27 = ats_caselptrlab_mac(anairiats_sum_1, arg5, atslab_0) ;
tmp28 = ats_caselptrlab_mac(anairiats_sum_1, arg5, atslab_1) ;
tmp30 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, tmp27), atslab_e0fftag_node) ;
do {
/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)tmp30)->tag != 2) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp31 = ats_caselptrlab_mac(anairiats_sum_2, tmp30, atslab_0) ;
tmp32 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp32, atslab_0, tmp31) ;
ats_selptrset_mac(anairiats_sum_1, tmp32, atslab_1, ats_ptrget_mac(ats_ptr_type, arg4)) ;
ats_ptrget_mac(ats_ptr_type, arg4) = tmp32 ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp30)->tag != 0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp33 = ats_caselptrlab_mac(anairiats_sum_3, tmp30, atslab_0) ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
tmp35 = atspre_eq_int_int (tmp33, 0) ;
if (tmp35) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil ;
} else {
/* empty */
} /* end of [if] */
tmp36 = atspre_eq_int_int (tmp33, 1) ;
if (tmp36) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)tmp30)->tag != 1) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp37 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_0) ;
tmp38 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_1) ;
tmp39 = name_is_all_1 (tmp38) ;
if (!tmp39) { goto __ats_lab_4_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
tmp40 = atspre_gt_int_int (tmp37, 0) ;
if (tmp40) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil ;
} else {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
} /* end of [if] */
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp30)->tag != 1) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp41 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_0) ;
tmp42 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_1) ;
tmp43 = name_is_nil_0 (tmp42) ;
if (!tmp43) { goto __ats_lab_5_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
tmp44 = atspre_gt_int_int (tmp41, 0) ;
if (tmp44) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
} else {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil ;
} /* end of [if] */
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)tmp30)->tag != 1) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp45 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_0) ;
tmp46 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_1) ;
tmp47 = name_is_lazy_10 (tmp46) ;
if (!tmp47) { goto __ats_lab_6_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
tmp49 = atspre_gt_int_int (tmp45, 0) ;
if (tmp49) {
tmp50 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp50 ;
} else {
/* empty */
} /* end of [if] */
tmp51 = atspre_eq_int_int (tmp45, 0) ;
if (tmp51) {
tmp52 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp52 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)tmp30)->tag != 1) { goto __ats_lab_16_0 ; }
__ats_lab_6_1:
tmp53 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_0) ;
tmp54 = ats_caselptrlab_mac(anairiats_sum_4, tmp30, atslab_1) ;
do {
/* branch: __ats_lab_7 */
__ats_lab_7_0:
__ats_lab_7_1:
tmp55 = name_is_ntm_2 (tmp54) ;
if (!tmp55) { goto __ats_lab_8_1 ; }
tmp57 = atspre_gt_int_int (tmp53, 0) ;
if (tmp57) {
tmp58 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ntm) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp58 ;
} else {
/* empty */
} /* end of [if] */
tmp59 = atspre_eq_int_int (tmp53, 0) ;
if (tmp59) {
tmp60 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ntm) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp60 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
__ats_lab_8_1:
tmp61 = name_is_exn_3 (tmp54) ;
if (!tmp61) { goto __ats_lab_9_1 ; }
tmp63 = atspre_gt_int_int (tmp53, 0) ;
if (tmp63) {
tmp64 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp64 ;
} else {
/* empty */
} /* end of [if] */
tmp65 = atspre_eq_int_int (tmp53, 0) ;
if (tmp65) {
tmp66 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp66 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
__ats_lab_9_1:
tmp67 = name_is_ref_4 (tmp54) ;
if (!tmp67) { goto __ats_lab_10_1 ; }
tmp69 = atspre_gt_int_int (tmp53, 0) ;
if (tmp69) {
tmp70 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp70 ;
} else {
/* empty */
} /* end of [if] */
tmp71 = atspre_eq_int_int (tmp53, 0) ;
if (tmp71) {
tmp72 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp72 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
__ats_lab_10_1:
tmp73 = name_is_wrt_5 (tmp54) ;
if (!tmp73) { goto __ats_lab_11_1 ; }
tmp75 = atspre_gt_int_int (tmp53, 0) ;
if (tmp75) {
tmp76 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp76 ;
} else {
/* empty */
} /* end of [if] */
tmp77 = atspre_eq_int_int (tmp53, 0) ;
if (tmp77) {
tmp78 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp78 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
__ats_lab_11_1:
tmp79 = name_is_exnref_6 (tmp54) ;
if (!tmp79) { goto __ats_lab_12_1 ; }
tmp81 = atspre_gt_int_int (tmp53, 0) ;
if (tmp81) {
tmp83 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp82 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (tmp83, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp82 ;
} else {
/* empty */
} /* end of [if] */
tmp84 = atspre_eq_int_int (tmp53, 0) ;
if (tmp84) {
tmp86 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp85 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (tmp86, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp85 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
__ats_lab_12_1:
tmp87 = name_is_exnwrt_7 (tmp54) ;
if (!tmp87) { goto __ats_lab_13_1 ; }
tmp89 = atspre_gt_int_int (tmp53, 0) ;
if (tmp89) {
tmp91 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp90 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (tmp91, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp90 ;
} else {
/* empty */
} /* end of [if] */
tmp92 = atspre_eq_int_int (tmp53, 0) ;
if (tmp92) {
tmp94 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp93 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (tmp94, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp93 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
__ats_lab_13_1:
tmp95 = name_is_exnrefwrt_8 (tmp54) ;
if (!tmp95) { goto __ats_lab_14_1 ; }
tmp97 = atspre_gt_int_int (tmp53, 0) ;
if (tmp97) {
tmp100 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp99 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (tmp100, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
tmp98 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (tmp99, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp98 ;
} else {
/* empty */
} /* end of [if] */
tmp101 = atspre_eq_int_int (tmp53, 0) ;
if (tmp101) {
tmp104 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_exn) ;
tmp103 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (tmp104, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
tmp102 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (tmp103, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp102 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_14 */
__ats_lab_14_0:
__ats_lab_14_1:
tmp105 = name_is_refwrt_9 (tmp54) ;
if (!tmp105) { goto __ats_lab_15_1 ; }
tmp107 = atspre_gt_int_int (tmp53, 0) ;
if (tmp107) {
tmp109 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
tmp108 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_del (tmp109, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp108 ;
} else {
/* empty */
} /* end of [if] */
tmp110 = atspre_eq_int_int (tmp53, 0) ;
if (tmp110) {
tmp112 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_ref) ;
tmp111 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_add (tmp112, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp111 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
__ats_lab_15_1:
/* tmp29 = */ loop_err_11 (tmp27, tmp54) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (((ats_sum_ptr_type)tmp30)->tag != 3) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
ats_ptrget_mac(ats_int_type, arg2) = 1 ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
if (((ats_sum_ptr_type)tmp30)->tag != 4) { goto __ats_lab_18_0 ; }
__ats_lab_17_1:
tmp113 = ats_caselptrlab_mac(anairiats_sum_3, tmp30, atslab_0) ;
ats_ptrget_mac(ats_int_type, arg1) = 1 ;
tmp114 = atspre_gt_int_int (tmp113, 0) ;
if (tmp114) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_18 */
__ats_lab_18_0:
if (((ats_sum_ptr_type)tmp30)->tag != 5) { goto __ats_lab_19_0 ; }
__ats_lab_18_1:
tmp115 = ats_caselptrlab_mac(anairiats_sum_5, tmp30, atslab_0) ;
tmp116 = ats_caselptrlab_mac(anairiats_sum_5, tmp30, atslab_1) ;
tmp118 = atspre_gte_int_int (tmp115, 0) ;
if (tmp118) {
ats_ptrget_mac(ats_int_type, arg1) = tmp115 ;
} else {
/* empty */
} /* end of [if] */
tmp120 = (ats_sum_ptr_type)0 ;
tmp119 = ATS_MALLOC(sizeof(anairiats_sum_6)) ;
ats_selptrset_mac(anairiats_sum_6, tmp119, atslab_0, tmp120) ;
ats_ptrget_mac(ats_ptr_type, arg0) = tmp119 ;
tmp121 = atspre_gt_int_int (tmp116, 0) ;
if (tmp121) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_19 */
__ats_lab_19_0:
// if (((ats_sum_ptr_type)tmp30)->tag != 6) { ats_deadcode_failure_handle () ; }
__ats_lab_19_1:
tmp122 = ats_caselptrlab_mac(anairiats_sum_7, tmp30, atslab_0) ;
tmp123 = ats_caselptrlab_mac(anairiats_sum_7, tmp30, atslab_1) ;
tmp124 = ats_caselptrlab_mac(anairiats_sum_7, tmp30, atslab_2) ;
tmp126 = atspre_gte_int_int (tmp122, 0) ;
if (tmp126) {
ats_ptrget_mac(ats_int_type, arg1) = tmp122 ;
} else {
/* empty */
} /* end of [if] */
tmp128 = ATS_MALLOC(sizeof(anairiats_sum_8)) ;
ats_selptrset_mac(anairiats_sum_8, tmp128, atslab_0, tmp123) ;
tmp127 = ATS_MALLOC(sizeof(anairiats_sum_6)) ;
ats_selptrset_mac(anairiats_sum_6, tmp127, atslab_0, tmp128) ;
ats_ptrget_mac(ats_ptr_type, arg0) = tmp127 ;
tmp129 = atspre_gt_int_int (tmp124, 0) ;
if (tmp129) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp17 ;
} else {
/* empty */
} /* end of [if] */
break ;
} while (0) ;
arg0 = arg0 ;
arg1 = arg1 ;
arg2 = arg2 ;
arg3 = arg3 ;
arg4 = arg4 ;
arg5 = tmp28 ;
goto __ats_lab_loop_12 ; // tail call
break ;

/* branch: __ats_lab_20 */
__ats_lab_20_0:
// if (arg5 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_20_1:
break ;
} while (0) ;
return /* (tmp26) */ ;
} /* end of [loop_12] */

/*
// /home/hwxi/research/Postiats/git/src/pats_trans1_effect.dats: 7442(line=225, offs=3) -- 7923(line=250, offs=4)
*/
ATSglobaldec()
anairiats_rec_9
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__e0fftaglst_tr (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (anairiats_rec_9, tmp130) ;
ATSlocal (ats_ptr_type, tmp131) ;
ATSlocal (ats_int_type, tmp132) ;
ATSlocal (ats_int_type, tmp133) ;
ATSlocal (ats_uint_type, tmp134) ;
ATSlocal (ats_ptr_type, tmp135) ;
// ATSlocal_void (tmp136) ;
ATSlocal (ats_ptr_type, tmp137) ;
ATSlocal (ats_bool_type, tmp138) ;
ATSlocal (ats_bool_type, tmp139) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__e0fftaglst_tr:
/* ats_ptr_type tmp131 ; */
tmp131 = (ats_sum_ptr_type)0 ;
/* ats_int_type tmp132 ; */
tmp132 = 0 ;
/* ats_int_type tmp133 ; */
tmp133 = 0 ;
/* ats_uint_type tmp134 ; */
tmp134 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil ;
/* ats_ptr_type tmp135 ; */
tmp135 = statmp17 ;
/* tmp136 = */ loop_12 ((&tmp131), (&tmp132), (&tmp133), (&tmp134), (&tmp135), arg0) ;
do {
/* branch: __ats_lab_21 */
__ats_lab_21_0:
__ats_lab_21_1:
tmp138 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__eq_effset_effset (tmp134, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_all) ;
if (!tmp138) { goto __ats_lab_22_1 ; }
tmp137 = (ats_sum_ptr_type)(&_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__EFFCSTall_0) ;
break ;

/* branch: __ats_lab_22 */
__ats_lab_22_0:
__ats_lab_22_1:
tmp139 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__eq_effset_effset (tmp134, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__effset_nil) ;
if (!tmp139) { goto __ats_lab_25_1 ; }
do {
/* branch: __ats_lab_23 */
__ats_lab_23_0:
if (tmp135 != (ats_sum_ptr_type)0) { goto __ats_lab_24_0 ; }
__ats_lab_23_1:
tmp137 = (ats_sum_ptr_type)(&_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__EFFCSTnil_1) ;
break ;

/* branch: __ats_lab_24 */
__ats_lab_24_0:
__ats_lab_24_1:
tmp137 = ATS_MALLOC(sizeof(anairiats_sum_10)) ;
((ats_sum_ptr_type)tmp137)->tag = 2 ;
ats_selptrset_mac(anairiats_sum_10, tmp137, atslab_0, tmp134) ;
ats_selptrset_mac(anairiats_sum_10, tmp137, atslab_1, tmp135) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_25 */
__ats_lab_25_0:
__ats_lab_25_1:
tmp137 = ATS_MALLOC(sizeof(anairiats_sum_10)) ;
((ats_sum_ptr_type)tmp137)->tag = 2 ;
ats_selptrset_mac(anairiats_sum_10, tmp137, atslab_0, tmp134) ;
ats_selptrset_mac(anairiats_sum_10, tmp137, atslab_1, tmp135) ;
break ;
} while (0) ;
tmp130.atslab_0 = tmp131 ;
tmp130.atslab_1 = tmp132 ;
tmp130.atslab_2 = tmp133 ;
tmp130.atslab_3 = tmp137 ;

return (tmp130) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__e0fftaglst_tr] */

/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_effect_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_effect_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */
ATS_GC_MARKROOT(&statmp17, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp17 = (ats_sum_ptr_type)0 ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_trans1_effect_dats.c] */
