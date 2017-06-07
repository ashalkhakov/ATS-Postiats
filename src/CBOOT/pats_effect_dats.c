/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-6-5: 20h:18m
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
/* external codes at top */
/* type definitions */
typedef struct {
ats_uint_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_0 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_nil_1) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_assert_errmsg) (ats_bool_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_string_append) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_bool_type, atspre_neg_bool) (ats_bool_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_uint_type, atspre_add_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_uint_type, atspre_lnot_uint) (ats_uint_type) ;
ATSextern_fun(ats_uint_type, atspre_land_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_uint_type, atspre_lor_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_uint_type, atspre_lsl_uint_int1) (ats_uint_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_prerr_string) (ats_ptr_type) ;
ATSextern_fun(ats_varet_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__abort_interr) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__prerr_location) (ats_ptr_type) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_get_name) (ats_uint_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effect) (ats_ptr_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect) (ats_uint_type, ats_uint_type) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all) ;
ATSextern_val(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_sing) (ats_uint_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil) (ats_uint_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isall) (ats_uint_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_cmpl) (ats_uint_type) ;
ATSextern_fun(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_inter) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_is_inter) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset) (ats_ptr_type, ats_uint_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__sasp__effset_t0ype = 0 ;
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__sasp__effect_t0ype = 0 ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ATSglobal(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effectlst_all) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ntm) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_exn) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ref) ;
ATSglobal(ats_uint_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_wrt) ;

/* internal function declarations */
static
ats_void_type prerr_FILENAME_01858_ () ;
static
ats_void_type loop_21 (ats_ptr_type arg0, ats_uint_type arg1, ats_uint_type arg2, ats_uint_type arg3, ats_ref_type arg4) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp1) ;
ATSstatic (ats_ptr_type, statmp2) ;
ATSstatic (ats_ptr_type, statmp3) ;
ATSstatic (ats_uint_type, statmp10) ;
ATSstatic (ats_uint_type, statmp11) ;
ATSstatic (ats_uint_type, statmp12) ;
ATSstatic (ats_uint_type, statmp13) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 1547(line=42, offs=28) -- 1571(line=42, offs=52)
*/
ATSstaticdec()
ats_void_type
prerr_FILENAME_01858_ () {
/* local vardec */
// ATSlocal_void (tmp0) ;

__ats_lab_prerr_FILENAME_01858_:
/* tmp0 = */ atspre_prerr_string (ATSstrcst("pats_effect")) ;
return /* (tmp0) */ ;
} /* end of [prerr_FILENAME_01858_] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 2319(line=79, offs=18) -- 2359(line=79, offs=58)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp4) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect:
tmp4 = atspre_eq_uint_uint (arg0, arg1) ;
return (tmp4) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 2410(line=85, offs=3) -- 2654(line=98, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_get_name (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp5) ;
// ATSlocal_void (tmp6) ;
ATSlocal (ats_ptr_type, tmp7) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_get_name:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (ats_castfn_mac(ats_int_type, arg0) != 0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp5 = ATSstrcst("ntm") ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (ats_castfn_mac(ats_int_type, arg0) != 1) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp5 = ATSstrcst("exn") ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (ats_castfn_mac(ats_int_type, arg0) != 2) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp5 = ATSstrcst("ref") ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (ats_castfn_mac(ats_int_type, arg0) != 3) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp5 = ATSstrcst("wrt") ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
__ats_lab_4_1:
tmp7 = atspre_string_append ("/home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 2576(line=96, offs=16) -- 2592(line=96, offs=32)", ATSstrcst("\n")) ;
/* tmp6 = */ atspre_assert_errmsg (ats_false_bool, tmp7) ;
/* tmp5 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__abort_interr () ;
break ;
} while (0) ;
return (tmp5) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_get_name] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 2729(line=103, offs=15) -- 2780(line=103, offs=66)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effect (ats_ptr_type arg0, ats_uint_type arg1) {
/* local vardec */
// ATSlocal_void (tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effect:
tmp9 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_get_name (arg1) ;
/* tmp8 = */ atspre_fprint_string (arg0, tmp9) ;
return /* (tmp8) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effect] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3145(line=119, offs=23) -- 3159(line=119, offs=37)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_sing (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_uint_type, tmp14) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_sing:
tmp14 = atspre_lsl_uint_uint (1u, arg0) ;
return (tmp14) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_sing] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3191(line=121, offs=28) -- 3231(line=121, offs=68)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp15) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset:
tmp15 = atspre_eq_uint_uint (arg0, arg1) ;
return (tmp15) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effset_effset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3277(line=125, offs=22) -- 3302(line=125, offs=47)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_uint_type, tmp16) ;
ATSlocal (ats_uint_type, tmp17) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add:
tmp17 = atspre_lsl_uint_uint (1u, arg1) ;
tmp16 = atspre_lor_uint_uint (arg0, tmp17) ;
return (tmp16) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_add] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3325(line=126, offs=22) -- 3352(line=126, offs=49)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_uint_type, tmp18) ;
ATSlocal (ats_uint_type, tmp19) ;
ATSlocal (ats_uint_type, tmp20) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del:
tmp20 = atspre_lsl_uint_uint (1u, arg1) ;
tmp19 = atspre_lnot_uint (tmp20) ;
tmp18 = atspre_land_uint_uint (arg0, tmp19) ;
return (tmp18) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_del] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3399(line=131, offs=14) -- 3439(line=131, offs=54)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp21) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil:
tmp21 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect (arg0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil) ;
return (tmp21) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3463(line=133, offs=14) -- 3503(line=133, offs=54)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isall (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp22) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isall:
tmp22 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__eq_effect_effect (arg0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all) ;
return (tmp22) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isall] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3527(line=135, offs=14) -- 3598(line=136, offs=55)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isfin (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp23) ;
ATSlocal (ats_uint_type, tmp24) ;
ATSlocal (ats_uint_type, tmp25) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isfin:
tmp25 = atspre_lsl_uint_int1 (1u, 4) ;
tmp24 = atspre_land_uint_uint (arg0, tmp25) ;
tmp23 = atspre_eq_uint_uint (tmp24, 0u) ;
return (tmp23) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isfin] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3647(line=139, offs=14) -- 3720(line=140, offs=55)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_iscof (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp26) ;
ATSlocal (ats_uint_type, tmp27) ;
ATSlocal (ats_uint_type, tmp28) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_iscof:
tmp28 = atspre_lsl_uint_int1 (1u, 4) ;
tmp27 = atspre_land_uint_uint (arg0, tmp28) ;
tmp26 = atspre_lt_uint_uint (tmp27, 0u) ;
return (tmp26) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_iscof] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3791(line=146, offs=14) -- 3825(line=146, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ismem (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp29) ;
ATSlocal (ats_uint_type, tmp30) ;
ATSlocal (ats_uint_type, tmp31) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ismem:
tmp31 = atspre_lsl_uint_uint (1u, arg1) ;
tmp30 = atspre_land_uint_uint (arg0, tmp31) ;
tmp29 = atspre_gt_uint_uint (tmp30, 0u) ;
return (tmp29) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ismem] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3853(line=150, offs=3) -- 3898(line=150, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_supset (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp32) ;
ATSlocal (ats_uint_type, tmp33) ;
ATSlocal (ats_uint_type, tmp34) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_supset:
tmp34 = atspre_lnot_uint (arg0) ;
tmp33 = atspre_land_uint_uint (tmp34, arg1) ;
tmp32 = atspre_eq_uint_uint (tmp33, 0u) ;
return (tmp32) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_supset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 3952(line=155, offs=3) -- 3997(line=155, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_subset (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp35) ;
ATSlocal (ats_uint_type, tmp36) ;
ATSlocal (ats_uint_type, tmp37) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_subset:
tmp37 = atspre_lnot_uint (arg1) ;
tmp36 = atspre_land_uint_uint (arg0, tmp37) ;
tmp35 = atspre_eq_uint_uint (tmp36, 0u) ;
return (tmp35) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_subset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4051(line=159, offs=17) -- 4104(line=160, offs=41)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_is_inter (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp38) ;
ATSlocal (ats_bool_type, tmp39) ;
ATSlocal (ats_uint_type, tmp40) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_is_inter:
tmp40 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_inter (arg0, arg1) ;
tmp39 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil (tmp40) ;
tmp38 = atspre_neg_bool (tmp39) ;
return (tmp38) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_is_inter] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4157(line=164, offs=13) -- 4177(line=164, offs=33)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_cmpl (ats_uint_type arg0) {
/* local vardec */
ATSlocal (ats_uint_type, tmp41) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_cmpl:
tmp41 = atspre_lnot_uint (arg0) ;
return (tmp41) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_cmpl] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4204(line=168, offs=3) -- 4243(line=168, offs=42)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_diff (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_uint_type, tmp42) ;
ATSlocal (ats_uint_type, tmp43) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_diff:
tmp43 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_cmpl (arg1) ;
tmp42 = atspre_land_uint_uint (arg0, tmp43) ;
return (tmp42) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_diff] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4293(line=172, offs=14) -- 4318(line=172, offs=39)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_inter (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_uint_type, tmp44) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_inter:
tmp44 = atspre_land_uint_uint (arg0, arg1) ;
return (tmp44) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_inter] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4343(line=175, offs=14) -- 4370(line=175, offs=41)
*/
ATSglobaldec()
ats_uint_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_union (ats_uint_type arg0, ats_uint_type arg1) {
/* local vardec */
ATSlocal (ats_uint_type, tmp45) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_union:
tmp45 = atspre_lor_uint_uint (arg0, arg1) ;
return (tmp45) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_union] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4444(line=183, offs=5) -- 4838(line=201, offs=4)
*/
ATSstaticdec()
ats_void_type
loop_21 (ats_ptr_type arg0, ats_uint_type arg1, ats_uint_type arg2, ats_uint_type arg3, ats_ref_type arg4) {
/* local vardec */
// ATSlocal_void (tmp47) ;
ATSlocal (ats_bool_type, tmp48) ;
ATSlocal (ats_bool_type, tmp49) ;
ATSlocal (ats_uint_type, tmp50) ;
// ATSlocal_void (tmp51) ;
// ATSlocal_void (tmp52) ;
ATSlocal (ats_bool_type, tmp53) ;
ATSlocal (ats_int_type, tmp54) ;
ATSlocal (ats_uint_type, tmp55) ;

__ats_lab_loop_21:
tmp48 = atspre_lt_uint_uint (arg3, arg2) ;
if (tmp48) {
tmp50 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_sing (arg3) ;
tmp49 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_is_inter (arg1, tmp50) ;
if (tmp49) {
tmp53 = atspre_gt_int_int (ats_ptrget_mac(ats_int_type, arg4), 0) ;
if (tmp53) {
/* tmp52 = */ atspre_fprint_string (arg0, ATSstrcst(", ")) ;
} else {
/* empty */
} /* end of [if] */
tmp54 = atspre_add_int_int (ats_ptrget_mac(ats_int_type, arg4), 1) ;
ats_ptrget_mac(ats_int_type, arg4) = tmp54 ;
/* tmp51 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effect (arg0, arg3) ;
} else {
/* empty */
} /* end of [if] */
tmp55 = atspre_add_uint_uint (arg3, 1u) ;
arg0 = arg0 ;
arg1 = arg1 ;
arg2 = arg2 ;
arg3 = tmp55 ;
arg4 = arg4 ;
goto __ats_lab_loop_21 ; // tail call
} else {
/* empty */
} /* end of [if] */
return /* (tmp47) */ ;
} /* end of [loop_21] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 4420(line=181, offs=3) -- 5164(line=218, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset (ats_ptr_type arg0, ats_uint_type arg1) {
/* local vardec */
// ATSlocal_void (tmp46) ;
ATSlocal (ats_int_type, tmp56) ;
ATSlocal (ats_bool_type, tmp57) ;
ATSlocal (ats_bool_type, tmp58) ;
// ATSlocal_void (tmp59) ;
// ATSlocal_void (tmp60) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset:
/* ats_int_type tmp56 ; */
tmp56 = 0 ;
do {
/* branch: __ats_lab_5 */
__ats_lab_5_0:
__ats_lab_5_1:
tmp57 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isnil (arg1) ;
if (!tmp57) { goto __ats_lab_6_1 ; }
/* tmp46 = */ atspre_fprint_string (arg0, ATSstrcst("0")) ;
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
__ats_lab_6_1:
tmp58 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_isall (arg1) ;
if (!tmp58) { goto __ats_lab_7_1 ; }
/* tmp46 = */ atspre_fprint_string (arg0, ATSstrcst("1")) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
__ats_lab_7_1:
/* tmp59 = */ atspre_fprint_string (arg0, ATSstrcst("[")) ;
/* tmp60 = */ loop_21 (arg0, arg1, ats_castfn_mac(ats_uint_type, 4), 0u, (&tmp56)) ;
/* tmp46 = */ atspre_fprint_string (arg0, ATSstrcst("]")) ;
break ;
} while (0) ;
return /* (tmp46) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 5215(line=221, offs=14) -- 5250(line=221, offs=49)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__print_effset (ats_uint_type arg0) {
/* local vardec */
// ATSlocal_void (tmp61) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__print_effset:
/* tmp61 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset (stdout, arg0) ;
return /* (tmp61) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__print_effset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_effect.dats: 5274(line=223, offs=14) -- 5309(line=223, offs=49)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__prerr_effset (ats_uint_type arg0) {
/* local vardec */
// ATSlocal_void (tmp62) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__prerr_effset:
/* tmp62 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__fprint_effset (stderr, arg0) ;
return /* (tmp62) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__prerr_effset] */

/* static load function */

extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__staload_flag = 1 ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_errmsg_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */
ATS_GC_MARKROOT(&statmp1, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp2, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp3, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp10, sizeof(ats_uint_type)) ;
ATS_GC_MARKROOT(&statmp11, sizeof(ats_uint_type)) ;
ATS_GC_MARKROOT(&statmp12, sizeof(ats_uint_type)) ;
ATS_GC_MARKROOT(&statmp13, sizeof(ats_uint_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm = ats_castfn_mac(ats_uint_type, 0) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn = ats_castfn_mac(ats_uint_type, 1) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref = ats_castfn_mac(ats_uint_type, 2) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt = ats_castfn_mac(ats_uint_type, 3) ;
statmp1 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, statmp1, atslab_0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
statmp2 = &ats_selptr_mac(ats_castptr_mac(anairiats_sum_0, statmp1), atslab_1) ;
statmp3 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, statmp3, atslab_0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ats_ptrget_mac(ats_ptr_type, statmp2) = statmp3 ;
statmp2 = &ats_selptr_mac(ats_castptr_mac(anairiats_sum_0, statmp3), atslab_1) ;
statmp3 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, statmp3, atslab_0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ats_ptrget_mac(ats_ptr_type, statmp2) = statmp3 ;
statmp2 = &ats_selptr_mac(ats_castptr_mac(anairiats_sum_0, statmp3), atslab_1) ;
statmp3 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, statmp3, atslab_0, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ats_ptrget_mac(ats_ptr_type, statmp2) = statmp3 ;
statmp2 = &ats_selptr_mac(ats_castptr_mac(anairiats_sum_0, statmp3), atslab_1) ;
statmp3 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, statmp2) = statmp3 ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effectlst_all, sizeof(ats_ptr_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effectlst_all = statmp1 ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_nil = ats_castfn_mac(ats_uint_type, 0) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_all = ats_castfn_mac(ats_uint_type, -1) ;
statmp10 = atspre_lsl_uint_uint (1u, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ntm) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ntm, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ntm = statmp10 ;
statmp11 = atspre_lsl_uint_uint (1u, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_exn) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_exn, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_exn = statmp11 ;
statmp12 = atspre_lsl_uint_uint (1u, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_ref) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ref, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_ref = statmp12 ;
statmp13 = atspre_lsl_uint_uint (1u, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effect_wrt) ;
ATS_GC_MARKROOT(&_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_wrt, sizeof(ats_uint_type)) ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_effect_2esats__effset_wrt = statmp13 ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_effect_dats.c] */
