/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2016-5-13: 12h:53m
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
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__None_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__Some_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__FUNCLOfun_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__FUNCLOclo_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGint_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGcst_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGvar_2) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGprf_3) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGlin_4) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGfun_5) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__E0FFTAGclo_6) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__EFFCSTall_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__EFFCSTnil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__EFFCSTset_2) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_prerr_newline) () ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_string_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_prerr_string) (ats_ptr_type) ;
ATSextern_fun(ats_varet_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__abort_interr) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__prerr_location) (ats_ptr_type) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ATSextern_val(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add) (ats_uint_type, ats_int_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del) (ats_uint_type, ats_int_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type prerr_FILENAME_01889_ () ;
static
ats_bool_type name_is_nil_1 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_all_2 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_ntm_3 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exn_4 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_ref_5 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_wrt_6 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnref_7 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnwrt_8 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_exnrefwrt_9 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_refwrt_10 (ats_ptr_type arg0) ;
static
ats_bool_type name_is_lazy_11 (ats_ptr_type arg0) ;
static
ats_void_type prerr_error1_loc_01892_ (ats_ptr_type arg0) ;
static
ats_void_type loop_err_12 (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_void_type loop_14 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ref_type arg3, ats_ref_type arg4, ats_ptr_type arg5) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp18) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 1598(line=46, offs=28) -- 1629(line=46, offs=59)
*/
ATSstaticdec()
ats_void_type
prerr_FILENAME_01889_ () {
/* local vardec */
// ATSlocal_void (tmp0) ;

__ats_lab_prerr_FILENAME_01889_:
/* tmp0 = */ atspre_prerr_string (ATSstrcst("pats_trans1_staexp")) ;
return /* (tmp0) */ ;
} /* end of [prerr_FILENAME_01889_] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 1838(line=63, offs=4) -- 1916(line=64, offs=44)
*/
ATSstaticdec()
ats_bool_type
name_is_nil_1 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp1) ;
ATSlocal (ats_bool_type, tmp2) ;

__ats_lab_name_is_nil_1:
tmp2 = atspre_eq_string_string (arg0, ATSstrcst("0")) ;
if (tmp2) {
tmp1 = ats_true_bool ;
} else {
tmp1 = atspre_eq_string_string (arg0, ATSstrcst("nil")) ;
} /* end of [if] */
return (tmp1) ;
} /* end of [name_is_nil_1] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 1920(line=65, offs=4) -- 1998(line=66, offs=44)
*/
ATSstaticdec()
ats_bool_type
name_is_all_2 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp3) ;
ATSlocal (ats_bool_type, tmp4) ;

__ats_lab_name_is_all_2:
tmp4 = atspre_eq_string_string (arg0, ATSstrcst("1")) ;
if (tmp4) {
tmp3 = ats_true_bool ;
} else {
tmp3 = atspre_eq_string_string (arg0, ATSstrcst("all")) ;
} /* end of [if] */
return (tmp3) ;
} /* end of [name_is_all_2] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2003(line=68, offs=4) -- 2087(line=69, offs=50)
*/
ATSstaticdec()
ats_bool_type
name_is_ntm_3 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp5) ;
ATSlocal (ats_bool_type, tmp6) ;

__ats_lab_name_is_ntm_3:
tmp6 = atspre_eq_string_string (arg0, ATSstrcst("ntm")) ;
if (tmp6) {
tmp5 = ats_true_bool ;
} else {
tmp5 = atspre_eq_string_string (arg0, ATSstrcst("nonterm")) ;
} /* end of [if] */
return (tmp5) ;
} /* end of [name_is_ntm_3] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2092(line=71, offs=4) -- 2178(line=72, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_exn_4 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp7) ;
ATSlocal (ats_bool_type, tmp8) ;

__ats_lab_name_is_exn_4:
tmp8 = atspre_eq_string_string (arg0, ATSstrcst("exn")) ;
if (tmp8) {
tmp7 = ats_true_bool ;
} else {
tmp7 = atspre_eq_string_string (arg0, ATSstrcst("exception")) ;
} /* end of [if] */
return (tmp7) ;
} /* end of [name_is_exn_4] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2182(line=73, offs=4) -- 2267(line=74, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_ref_5 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp9) ;
ATSlocal (ats_bool_type, tmp10) ;

__ats_lab_name_is_ref_5:
tmp10 = atspre_eq_string_string (arg0, ATSstrcst("ref")) ;
if (tmp10) {
tmp9 = ats_true_bool ;
} else {
tmp9 = atspre_eq_string_string (arg0, ATSstrcst("reference")) ;
} /* end of [if] */
return (tmp9) ;
} /* end of [name_is_ref_5] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2271(line=75, offs=4) -- 2353(line=76, offs=48)
*/
ATSstaticdec()
ats_bool_type
name_is_wrt_6 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp11) ;
ATSlocal (ats_bool_type, tmp12) ;

__ats_lab_name_is_wrt_6:
tmp12 = atspre_eq_string_string (arg0, ATSstrcst("wrt")) ;
if (tmp12) {
tmp11 = ats_true_bool ;
} else {
tmp11 = atspre_eq_string_string (arg0, ATSstrcst("write")) ;
} /* end of [if] */
return (tmp11) ;
} /* end of [name_is_wrt_6] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2358(line=78, offs=4) -- 2411(line=78, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_exnref_7 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp13) ;

__ats_lab_name_is_exnref_7:
tmp13 = atspre_eq_string_string (arg0, ATSstrcst("exnref")) ;
return (tmp13) ;
} /* end of [name_is_exnref_7] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2415(line=79, offs=4) -- 2468(line=79, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_exnwrt_8 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp14) ;

__ats_lab_name_is_exnwrt_8:
tmp14 = atspre_eq_string_string (arg0, ATSstrcst("exnwrt")) ;
return (tmp14) ;
} /* end of [name_is_exnwrt_8] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2472(line=80, offs=4) -- 2531(line=80, offs=63)
*/
ATSstaticdec()
ats_bool_type
name_is_exnrefwrt_9 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp15) ;

__ats_lab_name_is_exnrefwrt_9:
tmp15 = atspre_eq_string_string (arg0, ATSstrcst("exnrefwrt")) ;
return (tmp15) ;
} /* end of [name_is_exnrefwrt_9] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2535(line=81, offs=4) -- 2588(line=81, offs=57)
*/
ATSstaticdec()
ats_bool_type
name_is_refwrt_10 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp16) ;

__ats_lab_name_is_refwrt_10:
tmp16 = atspre_eq_string_string (arg0, ATSstrcst("refwrt")) ;
return (tmp16) ;
} /* end of [name_is_refwrt_10] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2620(line=86, offs=4) -- 2668(line=86, offs=52)
*/
ATSstaticdec()
ats_bool_type
name_is_lazy_11 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp17) ;

__ats_lab_name_is_lazy_11:
tmp17 = atspre_eq_string_string (arg0, ATSstrcst("laz")) ;
return (tmp17) ;
} /* end of [name_is_lazy_11] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_errmsg.dats: 1977(line=66, offs=18) -- 2036(line=68, offs=2)
*/
ATSstaticdec()
ats_void_type
prerr_error1_loc_01892_ (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp21) ;
// ATSlocal_void (tmp22) ;

__ats_lab_prerr_error1_loc_01892_:
/* tmp22 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__prerr_location (arg0) ;
/* tmp21 = */ atspre_prerr_string (ATSstrcst(": error(1)")) ;
return /* (tmp21) */ ;
} /* end of [prerr_error1_loc_01892_] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 2765(line=97, offs=1) -- 3001(line=110, offs=2)
*/
ATSstaticdec()
ats_void_type
loop_err_12 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp19) ;
// ATSlocal_void (tmp20) ;
ATSlocal (ats_ptr_type, tmp23) ;
// ATSlocal_void (tmp24) ;
// ATSlocal_void (tmp25) ;
// ATSlocal_void (tmp26) ;
// ATSlocal_void (tmp27) ;

__ats_lab_loop_err_12:
tmp23 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_e0fftag_loc) ;
/* tmp20 = */ prerr_error1_loc_01892_ (tmp23) ;
/* tmp24 = */ atspre_prerr_string (ATSstrcst(": unrecognized effect constant: [")) ;
/* tmp25 = */ atspre_prerr_string (arg1) ;
/* tmp26 = */ atspre_prerr_string (ATSstrcst("]")) ;
/* tmp27 = */ atspre_prerr_newline () ;
/* tmp19 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__abort_interr () ;
return /* (tmp19) */ ;
} /* end of [loop_err_12] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 3031(line=112, offs=5) -- 7510(line=234, offs=4)
*/
ATSstaticdec()
ats_void_type
loop_14 (ats_ref_type arg0, ats_ref_type arg1, ats_ref_type arg2, ats_ref_type arg3, ats_ref_type arg4, ats_ptr_type arg5) {
/* local vardec */
// ATSlocal_void (tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
// ATSlocal_void (tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_int_type, tmp35) ;
ATSlocal (ats_bool_type, tmp37) ;
ATSlocal (ats_bool_type, tmp38) ;
ATSlocal (ats_int_type, tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_bool_type, tmp41) ;
ATSlocal (ats_bool_type, tmp42) ;
ATSlocal (ats_int_type, tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;
ATSlocal (ats_bool_type, tmp45) ;
ATSlocal (ats_bool_type, tmp46) ;
ATSlocal (ats_int_type, tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_bool_type, tmp49) ;
ATSlocal (ats_bool_type, tmp51) ;
ATSlocal (ats_uint_type, tmp52) ;
ATSlocal (ats_bool_type, tmp53) ;
ATSlocal (ats_uint_type, tmp54) ;
ATSlocal (ats_int_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
ATSlocal (ats_bool_type, tmp57) ;
ATSlocal (ats_bool_type, tmp59) ;
ATSlocal (ats_uint_type, tmp60) ;
ATSlocal (ats_bool_type, tmp61) ;
ATSlocal (ats_uint_type, tmp62) ;
ATSlocal (ats_bool_type, tmp63) ;
ATSlocal (ats_bool_type, tmp65) ;
ATSlocal (ats_uint_type, tmp66) ;
ATSlocal (ats_bool_type, tmp67) ;
ATSlocal (ats_uint_type, tmp68) ;
ATSlocal (ats_bool_type, tmp69) ;
ATSlocal (ats_bool_type, tmp71) ;
ATSlocal (ats_uint_type, tmp72) ;
ATSlocal (ats_bool_type, tmp73) ;
ATSlocal (ats_uint_type, tmp74) ;
ATSlocal (ats_bool_type, tmp75) ;
ATSlocal (ats_bool_type, tmp77) ;
ATSlocal (ats_uint_type, tmp78) ;
ATSlocal (ats_bool_type, tmp79) ;
ATSlocal (ats_uint_type, tmp80) ;
ATSlocal (ats_bool_type, tmp81) ;
ATSlocal (ats_bool_type, tmp83) ;
ATSlocal (ats_uint_type, tmp84) ;
ATSlocal (ats_uint_type, tmp85) ;
ATSlocal (ats_bool_type, tmp86) ;
ATSlocal (ats_uint_type, tmp87) ;
ATSlocal (ats_uint_type, tmp88) ;
ATSlocal (ats_bool_type, tmp89) ;
ATSlocal (ats_bool_type, tmp91) ;
ATSlocal (ats_uint_type, tmp92) ;
ATSlocal (ats_uint_type, tmp93) ;
ATSlocal (ats_bool_type, tmp94) ;
ATSlocal (ats_uint_type, tmp95) ;
ATSlocal (ats_uint_type, tmp96) ;
ATSlocal (ats_bool_type, tmp97) ;
ATSlocal (ats_bool_type, tmp99) ;
ATSlocal (ats_uint_type, tmp100) ;
ATSlocal (ats_uint_type, tmp101) ;
ATSlocal (ats_uint_type, tmp102) ;
ATSlocal (ats_bool_type, tmp103) ;
ATSlocal (ats_uint_type, tmp104) ;
ATSlocal (ats_uint_type, tmp105) ;
ATSlocal (ats_uint_type, tmp106) ;
ATSlocal (ats_bool_type, tmp107) ;
ATSlocal (ats_bool_type, tmp109) ;
ATSlocal (ats_uint_type, tmp110) ;
ATSlocal (ats_uint_type, tmp111) ;
ATSlocal (ats_bool_type, tmp112) ;
ATSlocal (ats_uint_type, tmp113) ;
ATSlocal (ats_uint_type, tmp114) ;
ATSlocal (ats_int_type, tmp115) ;
ATSlocal (ats_bool_type, tmp116) ;
ATSlocal (ats_int_type, tmp117) ;
ATSlocal (ats_int_type, tmp118) ;
ATSlocal (ats_bool_type, tmp120) ;
ATSlocal (ats_ptr_type, tmp121) ;
ATSlocal (ats_ptr_type, tmp122) ;
ATSlocal (ats_bool_type, tmp123) ;
ATSlocal (ats_int_type, tmp124) ;
ATSlocal (ats_int_type, tmp125) ;
ATSlocal (ats_int_type, tmp126) ;
ATSlocal (ats_bool_type, tmp128) ;
ATSlocal (ats_ptr_type, tmp129) ;
ATSlocal (ats_ptr_type, tmp130) ;
ATSlocal (ats_bool_type, tmp131) ;

__ats_lab_loop_14:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (arg5 == (ats_sum_ptr_type)0) { goto __ats_lab_20_0 ; }
__ats_lab_0_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_1, arg5, atslab_0) ;
tmp30 = ats_caselptrlab_mac(anairiats_sum_1, arg5, atslab_1) ;
tmp32 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, tmp29), atslab_e0fftag_node) ;
do {
/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)tmp32)->tag != 2) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp33 = ats_caselptrlab_mac(anairiats_sum_2, tmp32, atslab_0) ;
tmp34 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp34, atslab_0, tmp33) ;
ats_selptrset_mac(anairiats_sum_1, tmp34, atslab_1, ats_ptrget_mac(ats_ptr_type, arg4)) ;
ats_ptrget_mac(ats_ptr_type, arg4) = tmp34 ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp32)->tag != 0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp35 = ats_caselptrlab_mac(anairiats_sum_3, tmp32, atslab_0) ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
tmp37 = atspre_eq_int_int (tmp35, 0) ;
if (tmp37) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil ;
} else {
/* empty */
} /* end of [if] */
tmp38 = atspre_eq_int_int (tmp35, 1) ;
if (tmp38) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)tmp32)->tag != 1) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp39 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_0) ;
tmp40 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_1) ;
tmp41 = name_is_all_2 (tmp40) ;
if (!tmp41) { goto __ats_lab_4_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
tmp42 = atspre_gt_int_int (tmp39, 0) ;
if (tmp42) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil ;
} else {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
} /* end of [if] */
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp32)->tag != 1) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp43 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_0) ;
tmp44 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_1) ;
tmp45 = name_is_nil_1 (tmp44) ;
if (!tmp45) { goto __ats_lab_5_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
tmp46 = atspre_gt_int_int (tmp43, 0) ;
if (tmp46) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
} else {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil ;
} /* end of [if] */
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)tmp32)->tag != 1) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp47 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_0) ;
tmp48 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_1) ;
tmp49 = name_is_lazy_11 (tmp48) ;
if (!tmp49) { goto __ats_lab_6_1 ; }
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
tmp51 = atspre_gt_int_int (tmp47, 0) ;
if (tmp51) {
tmp52 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp52 ;
} else {
/* empty */
} /* end of [if] */
tmp53 = atspre_eq_int_int (tmp47, 0) ;
if (tmp53) {
tmp54 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp54 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)tmp32)->tag != 1) { goto __ats_lab_16_0 ; }
__ats_lab_6_1:
tmp55 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_0) ;
tmp56 = ats_caselptrlab_mac(anairiats_sum_4, tmp32, atslab_1) ;
do {
/* branch: __ats_lab_7 */
__ats_lab_7_0:
__ats_lab_7_1:
tmp57 = name_is_ntm_3 (tmp56) ;
if (!tmp57) { goto __ats_lab_8_1 ; }
tmp59 = atspre_gt_int_int (tmp55, 0) ;
if (tmp59) {
tmp60 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp60 ;
} else {
/* empty */
} /* end of [if] */
tmp61 = atspre_eq_int_int (tmp55, 0) ;
if (tmp61) {
tmp62 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp62 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
__ats_lab_8_1:
tmp63 = name_is_exn_4 (tmp56) ;
if (!tmp63) { goto __ats_lab_9_1 ; }
tmp65 = atspre_gt_int_int (tmp55, 0) ;
if (tmp65) {
tmp66 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp66 ;
} else {
/* empty */
} /* end of [if] */
tmp67 = atspre_eq_int_int (tmp55, 0) ;
if (tmp67) {
tmp68 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp68 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
__ats_lab_9_1:
tmp69 = name_is_ref_5 (tmp56) ;
if (!tmp69) { goto __ats_lab_10_1 ; }
tmp71 = atspre_gt_int_int (tmp55, 0) ;
if (tmp71) {
tmp72 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp72 ;
} else {
/* empty */
} /* end of [if] */
tmp73 = atspre_eq_int_int (tmp55, 0) ;
if (tmp73) {
tmp74 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp74 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
__ats_lab_10_1:
tmp75 = name_is_wrt_6 (tmp56) ;
if (!tmp75) { goto __ats_lab_11_1 ; }
tmp77 = atspre_gt_int_int (tmp55, 0) ;
if (tmp77) {
tmp78 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp78 ;
} else {
/* empty */
} /* end of [if] */
tmp79 = atspre_eq_int_int (tmp55, 0) ;
if (tmp79) {
tmp80 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp80 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
__ats_lab_11_1:
tmp81 = name_is_exnref_7 (tmp56) ;
if (!tmp81) { goto __ats_lab_12_1 ; }
tmp83 = atspre_gt_int_int (tmp55, 0) ;
if (tmp83) {
tmp85 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp84 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (tmp85, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp84 ;
} else {
/* empty */
} /* end of [if] */
tmp86 = atspre_eq_int_int (tmp55, 0) ;
if (tmp86) {
tmp88 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp87 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (tmp88, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp87 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
__ats_lab_12_1:
tmp89 = name_is_exnwrt_8 (tmp56) ;
if (!tmp89) { goto __ats_lab_13_1 ; }
tmp91 = atspre_gt_int_int (tmp55, 0) ;
if (tmp91) {
tmp93 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp92 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (tmp93, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp92 ;
} else {
/* empty */
} /* end of [if] */
tmp94 = atspre_eq_int_int (tmp55, 0) ;
if (tmp94) {
tmp96 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp95 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (tmp96, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp95 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
__ats_lab_13_1:
tmp97 = name_is_exnrefwrt_9 (tmp56) ;
if (!tmp97) { goto __ats_lab_14_1 ; }
tmp99 = atspre_gt_int_int (tmp55, 0) ;
if (tmp99) {
tmp102 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp101 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (tmp102, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
tmp100 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (tmp101, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp100 ;
} else {
/* empty */
} /* end of [if] */
tmp103 = atspre_eq_int_int (tmp55, 0) ;
if (tmp103) {
tmp106 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
tmp105 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (tmp106, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
tmp104 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (tmp105, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp104 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_14 */
__ats_lab_14_0:
__ats_lab_14_1:
tmp107 = name_is_refwrt_10 (tmp56) ;
if (!tmp107) { goto __ats_lab_15_1 ; }
tmp109 = atspre_gt_int_int (tmp55, 0) ;
if (tmp109) {
tmp111 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
tmp110 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (tmp111, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp110 ;
} else {
/* empty */
} /* end of [if] */
tmp112 = atspre_eq_int_int (tmp55, 0) ;
if (tmp112) {
tmp114 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_ptrget_mac(ats_uint_type, arg3), _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
tmp113 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (tmp114, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_uint_type, arg3) = tmp113 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
__ats_lab_15_1:
/* tmp31 = */ loop_err_12 (tmp29, tmp56) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (((ats_sum_ptr_type)tmp32)->tag != 3) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
ats_ptrget_mac(ats_int_type, arg2) = 1 ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
if (((ats_sum_ptr_type)tmp32)->tag != 4) { goto __ats_lab_18_0 ; }
__ats_lab_17_1:
tmp115 = ats_caselptrlab_mac(anairiats_sum_3, tmp32, atslab_0) ;
ats_ptrget_mac(ats_int_type, arg1) = 1 ;
tmp116 = atspre_gt_int_int (tmp115, 0) ;
if (tmp116) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_18 */
__ats_lab_18_0:
if (((ats_sum_ptr_type)tmp32)->tag != 5) { goto __ats_lab_19_0 ; }
__ats_lab_18_1:
tmp117 = ats_caselptrlab_mac(anairiats_sum_5, tmp32, atslab_0) ;
tmp118 = ats_caselptrlab_mac(anairiats_sum_5, tmp32, atslab_1) ;
tmp120 = atspre_gte_int_int (tmp117, 0) ;
if (tmp120) {
ats_ptrget_mac(ats_int_type, arg1) = tmp117 ;
} else {
/* empty */
} /* end of [if] */
tmp122 = (ats_sum_ptr_type)0 ;
tmp121 = ATS_MALLOC(sizeof(anairiats_sum_6)) ;
ats_selptrset_mac(anairiats_sum_6, tmp121, atslab_0, tmp122) ;
ats_ptrget_mac(ats_ptr_type, arg0) = tmp121 ;
tmp123 = atspre_gt_int_int (tmp118, 0) ;
if (tmp123) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
} else {
/* empty */
} /* end of [if] */
break ;

/* branch: __ats_lab_19 */
__ats_lab_19_0:
// if (((ats_sum_ptr_type)tmp32)->tag != 6) { ats_deadcode_failure_handle () ; }
__ats_lab_19_1:
tmp124 = ats_caselptrlab_mac(anairiats_sum_7, tmp32, atslab_0) ;
tmp125 = ats_caselptrlab_mac(anairiats_sum_7, tmp32, atslab_1) ;
tmp126 = ats_caselptrlab_mac(anairiats_sum_7, tmp32, atslab_2) ;
tmp128 = atspre_gte_int_int (tmp124, 0) ;
if (tmp128) {
ats_ptrget_mac(ats_int_type, arg1) = tmp124 ;
} else {
/* empty */
} /* end of [if] */
tmp130 = ATS_MALLOC(sizeof(anairiats_sum_8)) ;
ats_selptrset_mac(anairiats_sum_8, tmp130, atslab_0, tmp125) ;
tmp129 = ATS_MALLOC(sizeof(anairiats_sum_6)) ;
ats_selptrset_mac(anairiats_sum_6, tmp129, atslab_0, tmp130) ;
ats_ptrget_mac(ats_ptr_type, arg0) = tmp129 ;
tmp131 = atspre_gt_int_int (tmp126, 0) ;
if (tmp131) {
ats_ptrget_mac(ats_uint_type, arg3) = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all ;
ats_ptrget_mac(ats_ptr_type, arg4) = statmp18 ;
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
arg5 = tmp30 ;
goto __ats_lab_loop_14 ; // tail call
break ;

/* branch: __ats_lab_20 */
__ats_lab_20_0:
// if (arg5 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_20_1:
break ;
} while (0) ;
return /* (tmp28) */ ;
} /* end of [loop_14] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_trans1_effect.dats: 7579(line=240, offs=3) -- 8060(line=265, offs=4)
*/
ATSglobaldec()
anairiats_rec_9
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_2esats__e0fftaglst_tr (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (anairiats_rec_9, tmp132) ;
ATSlocal (ats_ptr_type, tmp133) ;
ATSlocal (ats_int_type, tmp134) ;
ATSlocal (ats_int_type, tmp135) ;
ATSlocal (ats_uint_type, tmp136) ;
ATSlocal (ats_ptr_type, tmp137) ;
// ATSlocal_void (tmp138) ;
ATSlocal (ats_ptr_type, tmp139) ;
ATSlocal (ats_bool_type, tmp140) ;
ATSlocal (ats_bool_type, tmp141) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_2esats__e0fftaglst_tr:
/* ats_ptr_type tmp133 ; */
tmp133 = (ats_sum_ptr_type)0 ;
/* ats_int_type tmp134 ; */
tmp134 = 0 ;
/* ats_int_type tmp135 ; */
tmp135 = 0 ;
/* ats_uint_type tmp136 ; */
tmp136 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil ;
/* ats_ptr_type tmp137 ; */
tmp137 = statmp18 ;
/* tmp138 = */ loop_14 ((&tmp133), (&tmp134), (&tmp135), (&tmp136), (&tmp137), arg0) ;
do {
/* branch: __ats_lab_21 */
__ats_lab_21_0:
__ats_lab_21_1:
tmp140 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset (tmp136, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all) ;
if (!tmp140) { goto __ats_lab_22_1 ; }
tmp139 = (ats_sum_ptr_type)(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__EFFCSTall_0) ;
break ;

/* branch: __ats_lab_22 */
__ats_lab_22_0:
__ats_lab_22_1:
tmp141 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset (tmp136, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil) ;
if (!tmp141) { goto __ats_lab_25_1 ; }
do {
/* branch: __ats_lab_23 */
__ats_lab_23_0:
if (tmp137 != (ats_sum_ptr_type)0) { goto __ats_lab_24_0 ; }
__ats_lab_23_1:
tmp139 = (ats_sum_ptr_type)(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__EFFCSTnil_1) ;
break ;

/* branch: __ats_lab_24 */
__ats_lab_24_0:
__ats_lab_24_1:
tmp139 = ATS_MALLOC(sizeof(anairiats_sum_10)) ;
((ats_sum_ptr_type)tmp139)->tag = 2 ;
ats_selptrset_mac(anairiats_sum_10, tmp139, atslab_0, tmp136) ;
ats_selptrset_mac(anairiats_sum_10, tmp139, atslab_1, tmp137) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_25 */
__ats_lab_25_0:
__ats_lab_25_1:
tmp139 = ATS_MALLOC(sizeof(anairiats_sum_10)) ;
((ats_sum_ptr_type)tmp139)->tag = 2 ;
ats_selptrset_mac(anairiats_sum_10, tmp139, atslab_0, tmp136) ;
ats_selptrset_mac(anairiats_sum_10, tmp139, atslab_1, tmp137) ;
break ;
} while (0) ;
tmp132.atslab_0 = tmp133 ;
tmp132.atslab_1 = tmp134 ;
tmp132.atslab_2 = tmp135 ;
tmp132.atslab_3 = tmp139 ;

return (tmp132) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_2esats__e0fftaglst_tr] */

/* static load function */

extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__staload_flag = 1 ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_effect_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */
ATS_GC_MARKROOT(&statmp18, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp18 = (ats_sum_ptr_type)0 ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_trans1_effect_dats.c] */
