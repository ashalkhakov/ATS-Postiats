/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-10-8:  9h:56m
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
/* external codes at top */
/* type definitions */
typedef struct {
int tag ;
ats_int_type atslab_0 ;
} anairiats_sum_0 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_1 ;

typedef struct {
ats_int_type atslab_0 ;
} anairiats_sum_2 ;

typedef struct {
ats_ptr_type atslab_0 ;
} anairiats_sum_3 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__Some_vt_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABint_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABsym_1) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_int_type, atspre_compare_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_int) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostrptr_int) (ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ieq) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ineq) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__compare_symbol_symbol) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__fprint_symbol) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_get_name) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label) (ats_ptr_type, ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__sasp__label_type = 0 ;

/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABint_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABsym_1) ;

/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 1673(line=54, offs=16) -- 1692(line=54, offs=35)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_int (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_int:
tmp0 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
((ats_sum_ptr_type)tmp0)->tag = 0 ;
ats_selptrset_mac(anairiats_sum_0, tmp0, atslab_0, arg0) ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_int] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 1719(line=56, offs=16) -- 1738(line=56, offs=35)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_sym (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp1) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_sym:
tmp1 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
((ats_sum_ptr_type)tmp1)->tag = 1 ;
ats_selptrset_mac(anairiats_sum_1, tmp1, atslab_0, arg0) ;
return (tmp1) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_sym] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 1790(line=61, offs=19) -- 1863(line=63, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_string (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_string:
tmp3 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string (arg0) ;
tmp2 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
((ats_sum_ptr_type)tmp2)->tag = 1 ;
ats_selptrset_mac(anairiats_sum_1, tmp2, atslab_0, tmp3) ;
return (tmp2) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_make_string] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 1939(line=68, offs=14) -- 1995(line=69, offs=50)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_int (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp4) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_int:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp4 = ats_true_bool ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (((ats_sum_ptr_type)arg0)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
tmp4 = ats_false_bool ;
break ;
} while (0) ;
return (tmp4) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_int] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2046(line=73, offs=15) -- 2108(line=74, offs=57)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_int (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_int_type, tmp6) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_int:
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp6 = ats_caselptrlab_mac(anairiats_sum_0, arg0, atslab_0) ;
tmp5 = ATS_MALLOC(sizeof(anairiats_sum_2)) ;
ats_selptrset_mac(anairiats_sum_2, tmp5, atslab_0, tmp6) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
__ats_lab_3_1:
tmp5 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp5) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_int] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2180(line=80, offs=14) -- 2236(line=81, offs=50)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_sym (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp7) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_sym:
do {
/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp7 = ats_false_bool ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
// if (((ats_sum_ptr_type)arg0)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_5_1:
tmp7 = ats_true_bool ;
break ;
} while (0) ;
return (tmp7) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_is_sym] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2287(line=85, offs=15) -- 2349(line=86, offs=57)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_sym (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_sym:
do {
/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp9 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp8 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp8, atslab_0, tmp9) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
__ats_lab_7_1:
tmp8 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp8) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_get_sym] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2423(line=93, offs=3) -- 2736(line=109, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_dotize (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_int_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_dotize:
do {
/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp12 = ats_caselptrlab_mac(anairiats_sum_0, arg0, atslab_0) ;
tmp13 = atspre_tostringf (ATSstrcst(".%i"), tmp12) ;
tmp11 = ats_castfn_mac(ats_ptr_type, tmp13) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
// if (((ats_sum_ptr_type)arg0)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_9_1:
tmp14 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp16 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_get_name (tmp14) ;
tmp15 = atspre_tostringf (ATSstrcst(".%s"), tmp16) ;
tmp11 = ats_castfn_mac(ats_ptr_type, tmp15) ;
break ;
} while (0) ;
tmp10 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string (tmp11) ;
return (tmp10) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__label_dotize] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2811(line=115, offs=3) -- 2854(line=115, offs=46)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__eq_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp17) ;
ATSlocal (ats_int_type, tmp18) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__eq_label_label:
tmp18 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label (arg0, arg1) ;
tmp17 = atspre_ieq (tmp18, 0) ;
return (tmp17) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__eq_label_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 2910(line=119, offs=3) -- 2954(line=119, offs=47)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__neq_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp19) ;
ATSlocal (ats_int_type, tmp20) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__neq_label_label:
tmp20 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label (arg0, arg1) ;
tmp19 = atspre_ineq (tmp20, 0) ;
return (tmp19) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__neq_label_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 3037(line=126, offs=3) -- 3362(line=148, offs=4)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp21) ;
ATSlocal (ats_int_type, tmp22) ;
ATSlocal (ats_int_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label:
do {
/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_12_1 ; }
__ats_lab_10_2:
tmp22 = ats_caselptrlab_mac(anairiats_sum_0, arg0, atslab_0) ;
tmp23 = ats_caselptrlab_mac(anairiats_sum_0, arg1, atslab_0) ;
tmp21 = atspre_compare_int_int (tmp22, tmp23) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
if (((ats_sum_ptr_type)arg0)->tag != 1) { goto __ats_lab_12_0 ; }
__ats_lab_11_1:
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_13_1 ; }
__ats_lab_11_2:
tmp24 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp25 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp21 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__compare_symbol_symbol (tmp24, tmp25) ;
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
// if (((ats_sum_ptr_type)arg1)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_12_2:
tmp21 = -1 ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
// if (((ats_sum_ptr_type)arg0)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_13_1:
// if (((ats_sum_ptr_type)arg1)->tag != 0) { ats_deadcode_failure_handle () ; }
__ats_lab_13_2:
tmp21 = 1 ;
break ;
} while (0) ;
return (tmp21) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__compare_label_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 3444(line=154, offs=3) -- 3598(line=163, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__tostring_label (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_int_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__tostring_label:
do {
/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (((ats_sum_ptr_type)arg0)->tag != 0) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp27 = ats_caselptrlab_mac(anairiats_sum_0, arg0, atslab_0) ;
tmp28 = atspre_tostrptr_int (tmp27) ;
tmp26 = ats_castfn_mac(ats_ptr_type, tmp28) ;
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
// if (((ats_sum_ptr_type)arg0)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_15_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp26 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_get_name (tmp29) ;
break ;
} while (0) ;
return (tmp26) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__tostring_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 3671(line=168, offs=12) -- 3704(line=168, offs=45)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__print_label (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp30) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__print_label:
/* tmp30 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label (stdout, arg0) ;
return /* (tmp30) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__print_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 3726(line=170, offs=12) -- 3759(line=170, offs=45)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__prerr_label (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp31) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__prerr_label:
/* tmp31 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label (stderr, arg0) ;
return /* (tmp31) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__prerr_label] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_label.dats: 3786(line=173, offs=14) -- 3899(line=177, offs=48)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp32) ;
ATSlocal (ats_int_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label:
do {
/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
tmp33 = ats_caselptrlab_mac(anairiats_sum_0, arg1, atslab_0) ;
/* tmp32 = */ atspre_fprint_int (arg0, tmp33) ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
// if (((ats_sum_ptr_type)arg1)->tag != 1) { ats_deadcode_failure_handle () ; }
__ats_lab_17_1:
tmp34 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
/* tmp32 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp34) ;
break ;
} while (0) ;
return /* (tmp32) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__fprint_label] */

/* static load function */

extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__staload_flag = 1 ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2esats__staload () ;

// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABint_0.tag = 0 ;
// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__LABsym_1.tag = 1 ;
return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_label_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_label_dats.c] */
