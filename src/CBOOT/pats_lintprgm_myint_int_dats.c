/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-11-6: 17h:45m
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

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"
/* external codes at top */

#include "pats_lintprgm_myint.cats"

/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_int_type, atspre_neg_int) (ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_sub_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_mul_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_div_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_mod_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_gcd_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_compare_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_int) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__intinf_get_int) (ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
intknd myint_make_int_02219_intknd (ats_int_type arg0) ;
static
intknd myint_make_intinf_02220_intknd (ats_ptr_type arg0) ;
static
ats_void_type myint_free_02221_intknd (intknd arg0) ;
static
intknd myint_copy_02222_intknd (intknd arg0) ;
static
intknd neg_myint_02223_intknd (intknd arg0) ;
static
intknd neg1_myint_02224_intknd (intknd arg0) ;
static
intknd add_myint_int_02225_intknd (intknd arg0, ats_int_type arg1) ;
static
intknd add01_myint_myint_02226_intknd (intknd arg0, intknd arg1) ;
static
intknd sub01_myint_myint_02227_intknd (intknd arg0, intknd arg1) ;
static
intknd mul01_myint_myint_02228_intknd (intknd arg0, intknd arg1) ;
static
intknd mul10_myint_myint_02229_intknd (intknd arg0, intknd arg1) ;
static
intknd mul11_myint_myint_02230_intknd (intknd arg0, intknd arg1) ;
static
intknd div01_myint_myint_02231_intknd (intknd arg0, intknd arg1) ;
static
intknd div11_myint_myint_02232_intknd (intknd arg0, intknd arg1) ;
static
intknd ediv01_myint_myint_02233_intknd (intknd arg0, intknd arg1) ;
static
intknd mod01_myint_myint_02234_intknd (intknd arg0, intknd arg1) ;
static
intknd mod11_myint_myint_02235_intknd (intknd arg0, intknd arg1) ;
static
intknd gcd01_myint_myint_02236_intknd (intknd arg0, intknd arg1) ;
static
ats_bool_type lt_myint_int_02237_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type lte_myint_int_02238_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type gt_myint_int_02239_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type gte_myint_int_02240_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type eq_myint_int_02241_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type neq_myint_int_02242_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_int_type compare_myint_int_02243_intknd (intknd arg0, ats_int_type arg1) ;
static
ats_bool_type lt_myint_myint_02244_intknd (intknd arg0, intknd arg1) ;
static
ats_bool_type lte_myint_myint_02245_intknd (intknd arg0, intknd arg1) ;
static
ats_bool_type gt_myint_myint_02246_intknd (intknd arg0, intknd arg1) ;
static
ats_bool_type gte_myint_myint_02247_intknd (intknd arg0, intknd arg1) ;
static
ats_void_type fprint_myint_02216_intknd (ats_ptr_type arg0, intknd arg1) ;
static
ats_void_type myintvec_free_02263_intknd (ats_ptr_type arg0, ats_int_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2166(line=78, offs=24) -- 2184(line=78, offs=42)
*/
ATSstaticdec()
intknd
myint_make_int_02219_intknd (ats_int_type arg0) {
/* local vardec */
ATSlocal (intknd, tmp0) ;

__ats_lab_myint_make_int_02219_intknd:
tmp0 = ats_castfn_mac(intknd, arg0) ;
return (tmp0) ;
} /* end of [myint_make_int_02219_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2223(line=81, offs=27) -- 2290(line=83, offs=4)
*/
ATSstaticdec()
intknd
myint_make_intinf_02220_intknd (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (intknd, tmp1) ;
ATSlocal (ats_int_type, tmp2) ;

__ats_lab_myint_make_intinf_02220_intknd:
tmp2 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__intinf_get_int (arg0) ;
tmp1 = ats_castfn_mac(intknd, tmp2) ;
return (tmp1) ;
} /* end of [myint_make_intinf_02220_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2377(line=88, offs=20) -- 2437(line=90, offs=4)
*/
ATSstaticdec()
ats_void_type
myint_free_02221_intknd (intknd arg0) {
/* local vardec */
// ATSlocal_void (tmp3) ;

__ats_lab_myint_free_02221_intknd:
return /* (tmp3) */ ;
} /* end of [myint_free_02221_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2491(line=92, offs=30) -- 2514(line=92, offs=53)
*/
ATSstaticdec()
intknd
myint_copy_02222_intknd (intknd arg0) {
/* local vardec */
ATSlocal (intknd, tmp4) ;

__ats_lab_myint_copy_02222_intknd:
tmp4 = ats_castfn_mac(intknd, arg0) ;
return (tmp4) ;
} /* end of [myint_copy_02222_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2566(line=97, offs=19) -- 2586(line=97, offs=39)
*/
ATSstaticdec()
intknd
neg_myint_02223_intknd (intknd arg0) {
/* local vardec */
ATSlocal (intknd, tmp5) ;
ATSlocal (ats_int_type, tmp6) ;

__ats_lab_neg_myint_02223_intknd:
tmp6 = atspre_neg_int (ats_castfn_mac(ats_int_type, arg0)) ;
tmp5 = ats_castfn_mac(intknd, tmp6) ;
return (tmp5) ;
} /* end of [neg_myint_02223_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2617(line=99, offs=20) -- 2637(line=99, offs=40)
*/
ATSstaticdec()
intknd
neg1_myint_02224_intknd (intknd arg0) {
/* local vardec */
ATSlocal (intknd, tmp7) ;
ATSlocal (ats_int_type, tmp8) ;

__ats_lab_neg1_myint_02224_intknd:
tmp8 = atspre_neg_int (ats_castfn_mac(ats_int_type, arg0)) ;
tmp7 = ats_castfn_mac(intknd, tmp8) ;
return (tmp7) ;
} /* end of [neg1_myint_02224_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2693(line=104, offs=23) -- 2719(line=104, offs=49)
*/
ATSstaticdec()
intknd
add_myint_int_02225_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (intknd, tmp9) ;
ATSlocal (ats_int_type, tmp10) ;

__ats_lab_add_myint_int_02225_intknd:
tmp10 = atspre_add_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
tmp9 = ats_castfn_mac(intknd, tmp10) ;
return (tmp9) ;
} /* end of [add_myint_int_02225_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2781(line=110, offs=3) -- 2841(line=112, offs=2)
*/
ATSstaticdec()
intknd
add01_myint_myint_02226_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp11) ;
ATSlocal (ats_int_type, tmp12) ;

__ats_lab_add01_myint_myint_02226_intknd:
tmp12 = atspre_add_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp11 = ats_castfn_mac(intknd, tmp12) ;
return (tmp11) ;
} /* end of [add01_myint_myint_02226_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 2917(line=116, offs=3) -- 2977(line=118, offs=2)
*/
ATSstaticdec()
intknd
sub01_myint_myint_02227_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp13) ;
ATSlocal (ats_int_type, tmp14) ;

__ats_lab_sub01_myint_myint_02227_intknd:
tmp14 = atspre_sub_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp13 = ats_castfn_mac(intknd, tmp14) ;
return (tmp13) ;
} /* end of [sub01_myint_myint_02227_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3072(line=123, offs=27) -- 3105(line=123, offs=60)
*/
ATSstaticdec()
intknd
mul01_myint_myint_02228_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp15) ;
ATSlocal (ats_int_type, tmp16) ;

__ats_lab_mul01_myint_myint_02228_intknd:
tmp16 = atspre_mul_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp15 = ats_castfn_mac(intknd, tmp16) ;
return (tmp15) ;
} /* end of [mul01_myint_myint_02228_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3143(line=125, offs=27) -- 3176(line=125, offs=60)
*/
ATSstaticdec()
intknd
mul10_myint_myint_02229_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp17) ;
ATSlocal (ats_int_type, tmp18) ;

__ats_lab_mul10_myint_myint_02229_intknd:
tmp18 = atspre_mul_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp17 = ats_castfn_mac(intknd, tmp18) ;
return (tmp17) ;
} /* end of [mul10_myint_myint_02229_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3214(line=127, offs=27) -- 3247(line=127, offs=60)
*/
ATSstaticdec()
intknd
mul11_myint_myint_02230_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp19) ;
ATSlocal (ats_int_type, tmp20) ;

__ats_lab_mul11_myint_myint_02230_intknd:
tmp20 = atspre_mul_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp19 = ats_castfn_mac(intknd, tmp20) ;
return (tmp19) ;
} /* end of [mul11_myint_myint_02230_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3309(line=133, offs=3) -- 3369(line=135, offs=2)
*/
ATSstaticdec()
intknd
div01_myint_myint_02231_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp21) ;
ATSlocal (ats_int_type, tmp22) ;

__ats_lab_div01_myint_myint_02231_intknd:
tmp22 = atspre_div_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp21 = ats_castfn_mac(intknd, tmp22) ;
return (tmp21) ;
} /* end of [div01_myint_myint_02231_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3445(line=138, offs=27) -- 3478(line=138, offs=60)
*/
ATSstaticdec()
intknd
div11_myint_myint_02232_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp23) ;
ATSlocal (ats_int_type, tmp24) ;

__ats_lab_div11_myint_myint_02232_intknd:
tmp24 = atspre_div_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp23 = ats_castfn_mac(intknd, tmp24) ;
return (tmp23) ;
} /* end of [div11_myint_myint_02232_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3520(line=142, offs=3) -- 3580(line=144, offs=2)
*/
ATSstaticdec()
intknd
ediv01_myint_myint_02233_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp25) ;
ATSlocal (ats_int_type, tmp26) ;

__ats_lab_ediv01_myint_myint_02233_intknd:
tmp26 = atspre_div_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp25 = ats_castfn_mac(intknd, tmp26) ;
return (tmp25) ;
} /* end of [ediv01_myint_myint_02233_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3678(line=150, offs=3) -- 3746(line=152, offs=2)
*/
ATSstaticdec()
intknd
mod01_myint_myint_02234_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp27) ;
ATSlocal (ats_int_type, tmp28) ;

__ats_lab_mod01_myint_myint_02234_intknd:
tmp28 = atspre_mod_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp27 = ats_castfn_mac(intknd, tmp28) ;
return (tmp27) ;
} /* end of [mod01_myint_myint_02234_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3822(line=155, offs=27) -- 3857(line=155, offs=62)
*/
ATSstaticdec()
intknd
mod11_myint_myint_02235_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp29) ;
ATSlocal (ats_int_type, tmp30) ;

__ats_lab_mod11_myint_myint_02235_intknd:
tmp30 = atspre_mod_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp29 = ats_castfn_mac(intknd, tmp30) ;
return (tmp29) ;
} /* end of [mod11_myint_myint_02235_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 3919(line=161, offs=3) -- 3987(line=163, offs=2)
*/
ATSstaticdec()
intknd
gcd01_myint_myint_02236_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (intknd, tmp31) ;
ATSlocal (ats_int_type, tmp32) ;

__ats_lab_gcd01_myint_myint_02236_intknd:
tmp32 = atspre_gcd_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
tmp31 = ats_castfn_mac(intknd, tmp32) ;
return (tmp31) ;
} /* end of [gcd01_myint_myint_02236_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4077(line=167, offs=32) -- 4098(line=167, offs=53)
*/
ATSstaticdec()
ats_bool_type
lt_myint_int_02237_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp33) ;

__ats_lab_lt_myint_int_02237_intknd:
tmp33 = atspre_lt_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp33) ;
} /* end of [lt_myint_int_02237_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4131(line=168, offs=33) -- 4153(line=168, offs=55)
*/
ATSstaticdec()
ats_bool_type
lte_myint_int_02238_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp34) ;

__ats_lab_lte_myint_int_02238_intknd:
tmp34 = atspre_lte_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp34) ;
} /* end of [lte_myint_int_02238_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4185(line=169, offs=32) -- 4206(line=169, offs=53)
*/
ATSstaticdec()
ats_bool_type
gt_myint_int_02239_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp35) ;

__ats_lab_gt_myint_int_02239_intknd:
tmp35 = atspre_gt_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp35) ;
} /* end of [gt_myint_int_02239_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4239(line=170, offs=33) -- 4261(line=170, offs=55)
*/
ATSstaticdec()
ats_bool_type
gte_myint_int_02240_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp36) ;

__ats_lab_gte_myint_int_02240_intknd:
tmp36 = atspre_gte_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp36) ;
} /* end of [gte_myint_int_02240_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4293(line=171, offs=32) -- 4314(line=171, offs=53)
*/
ATSstaticdec()
ats_bool_type
eq_myint_int_02241_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp37) ;

__ats_lab_eq_myint_int_02241_intknd:
tmp37 = atspre_eq_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp37) ;
} /* end of [eq_myint_int_02241_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4347(line=172, offs=33) -- 4369(line=172, offs=55)
*/
ATSstaticdec()
ats_bool_type
neq_myint_int_02242_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp38) ;

__ats_lab_neq_myint_int_02242_intknd:
tmp38 = atspre_neq_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp38) ;
} /* end of [neq_myint_int_02242_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4406(line=174, offs=27) -- 4436(line=174, offs=57)
*/
ATSstaticdec()
ats_int_type
compare_myint_int_02243_intknd (intknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp39) ;

__ats_lab_compare_myint_int_02243_intknd:
tmp39 = atspre_compare_int_int (ats_castfn_mac(ats_int_type, arg0), arg1) ;
return (tmp39) ;
} /* end of [compare_myint_int_02243_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4492(line=178, offs=34) -- 4521(line=178, offs=63)
*/
ATSstaticdec()
ats_bool_type
lt_myint_myint_02244_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp40) ;

__ats_lab_lt_myint_myint_02244_intknd:
tmp40 = atspre_lt_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
return (tmp40) ;
} /* end of [lt_myint_myint_02244_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4557(line=179, offs=35) -- 4587(line=179, offs=65)
*/
ATSstaticdec()
ats_bool_type
lte_myint_myint_02245_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp41) ;

__ats_lab_lte_myint_myint_02245_intknd:
tmp41 = atspre_lte_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
return (tmp41) ;
} /* end of [lte_myint_myint_02245_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4622(line=180, offs=34) -- 4651(line=180, offs=63)
*/
ATSstaticdec()
ats_bool_type
gt_myint_myint_02246_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp42) ;

__ats_lab_gt_myint_myint_02246_intknd:
tmp42 = atspre_gt_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
return (tmp42) ;
} /* end of [gt_myint_myint_02246_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4687(line=181, offs=35) -- 4717(line=181, offs=65)
*/
ATSstaticdec()
ats_bool_type
gte_myint_myint_02247_intknd (intknd arg0, intknd arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp43) ;

__ats_lab_gte_myint_myint_02247_intknd:
tmp43 = atspre_gte_int_int (ats_castfn_mac(ats_int_type, arg0), ats_castfn_mac(ats_int_type, arg1)) ;
return (tmp43) ;
} /* end of [gte_myint_myint_02247_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4772(line=186, offs=22) -- 4809(line=186, offs=59)
*/
ATSstaticdec()
ats_void_type
fprint_myint_02216_intknd (ats_ptr_type arg0, intknd arg1) {
/* local vardec */
// ATSlocal_void (tmp44) ;

__ats_lab_fprint_myint_02216_intknd:
/* tmp44 = */ atspre_fprint_int (arg0, ats_castfn_mac(ats_int_type, arg1)) ;
return /* (tmp44) */ ;
} /* end of [fprint_myint_02216_intknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_int.dats: 4870(line=192, offs=7) -- 5181(line=204, offs=4)
*/
ATSstaticdec()
ats_void_type
myintvec_free_02263_intknd (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;

__ats_lab_myintvec_free_02263_intknd:
tmp46 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, arg0), atslab_2) ;
/* tmp45 = */ atspre_array_ptr_free (tmp46) ;
return /* (tmp45) */ ;
} /* end of [myintvec_free_02263_intknd] */

/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
// extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__dynload () {
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_int_2edats__staload () ;

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

/* end of [pats_lintprgm_myint_int_dats.c] */
