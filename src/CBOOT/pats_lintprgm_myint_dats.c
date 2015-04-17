/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2015-4-16: 10h:44m
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
/* external codes at top */

#include "pats_lintprgm_myint.cats"

/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_ptr_type, atspre_ptr_alloc_tsz) (ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_neg1) (ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_add2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_sub2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_mul2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_fprint_mpz) (ats_ptr_type, ats_ref_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type fprint_myint_02226_gmpknd (ats_ptr_type arg0, gmpknd arg1) ;
static
ats_void_type print_myint_02227_gmpknd (gmpknd arg0) ;
static
ats_void_type prerr_myint_02228_gmpknd (gmpknd arg0) ;
static
gmpknd myint_make_int_02229_gmpknd (ats_int_type arg0) ;
static
gmpknd myint_make_intinf_02230_gmpknd (ats_ptr_type arg0) ;
static
gmpknd myint_copy_02232_gmpknd (gmpknd arg0) ;
static
ats_void_type myint_free_02231_gmpknd (gmpknd arg0) ;
static
gmpknd neg_myint_02233_gmpknd (gmpknd arg0) ;
static
gmpknd neg1_myint_02234_gmpknd (gmpknd arg0) ;
static
gmpknd add01_myint_myint_02236_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd sub01_myint_myint_02237_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd add_myint_int_02235_gmpknd (gmpknd arg0, ats_int_type arg1) ;
static
gmpknd mul01_myint_myint_02238_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd mul10_myint_myint_02239_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd mul11_myint_myint_02240_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd div01_myint_myint_02241_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd ediv01_myint_myint_02243_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd mod01_myint_myint_02244_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd mod11_myint_myint_02245_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
gmpknd gcd01_myint_myint_02246_gmpknd (gmpknd arg0, gmpknd arg1) ;
static
ats_int_type compare_myint_int_02253_gmpknd (gmpknd arg0, ats_int_type arg1) ;
static
ats_int_type compare_myint_myint_02258_gmpknd (gmpknd arg0, gmpknd arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 2251(line=82, offs=3) -- 2419(line=90, offs=4)
*/
ATSstaticdec()
ats_void_type
fprint_myint_02226_gmpknd (ats_ptr_type arg0, gmpknd arg1) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;

__ats_lab_fprint_myint_02226_gmpknd:
tmp1 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp0 = */ atslib_fprint_mpz (arg0, tmp1) ;
return /* (tmp0) */ ;
} /* end of [fprint_myint_02226_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 2486(line=93, offs=21) -- 2528(line=93, offs=63)
*/
ATSstaticdec()
ats_void_type
print_myint_02227_gmpknd (gmpknd arg0) {
/* local vardec */
// ATSlocal_void (tmp2) ;

__ats_lab_print_myint_02227_gmpknd:
/* tmp2 = */ fprint_myint_02226_gmpknd (stdout, arg0) ;
return /* (tmp2) */ ;
} /* end of [print_myint_02227_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 2559(line=95, offs=21) -- 2601(line=95, offs=63)
*/
ATSstaticdec()
ats_void_type
prerr_myint_02228_gmpknd (gmpknd arg0) {
/* local vardec */
// ATSlocal_void (tmp3) ;

__ats_lab_prerr_myint_02228_gmpknd:
/* tmp3 = */ fprint_myint_02226_gmpknd (stderr, arg0) ;
return /* (tmp3) */ ;
} /* end of [prerr_myint_02228_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 2659(line=100, offs=24) -- 2814(line=107, offs=4)
*/
ATSstaticdec()
gmpknd
myint_make_int_02229_gmpknd (ats_int_type arg0) {
/* local vardec */
ATSlocal (gmpknd, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;
// ATSlocal_void (tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;

__ats_lab_myint_make_int_02229_gmpknd:
tmp5 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp6 = ats_selsin_mac(tmp5, atslab_2) ;
/* tmp7 = */ atslib_mpz_init_set_int (tmp6, arg0) ;
tmp8 = tmp6 ;
tmp4 = ats_castfn_mac(gmpknd, tmp8) ;
return (tmp4) ;
} /* end of [myint_make_int_02229_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 3094(line=126, offs=27) -- 3321(line=135, offs=4)
*/
ATSstaticdec()
gmpknd
myint_make_intinf_02230_gmpknd (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (gmpknd, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
// ATSlocal_void (tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;

__ats_lab_myint_make_intinf_02230_gmpknd:
tmp10 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp11 = ats_selsin_mac(tmp10, atslab_2) ;
tmp12 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, arg0), atslab_2) ;
/* tmp13 = */ atslib_mpz_init_set_mpz (tmp11, tmp12) ;
tmp14 = tmp11 ;
tmp9 = ats_castfn_mac(gmpknd, tmp14) ;
return (tmp9) ;
} /* end of [myint_make_intinf_02230_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 3424(line=142, offs=20) -- 3667(line=151, offs=4)
*/
ATSstaticdec()
gmpknd
myint_copy_02232_gmpknd (gmpknd arg0) {
/* local vardec */
ATSlocal (gmpknd, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
// ATSlocal_void (tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;

__ats_lab_myint_copy_02232_gmpknd:
tmp16 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp17 = ats_selsin_mac(tmp16, atslab_2) ;
tmp19 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp18 = */ atslib_mpz_init_set_mpz (tmp17, tmp19) ;
tmp20 = tmp17 ;
tmp15 = ats_castfn_mac(gmpknd, tmp20) ;
return (tmp15) ;
} /* end of [myint_copy_02232_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 3750(line=156, offs=20) -- 3877(line=162, offs=4)
*/
ATSstaticdec()
ats_void_type
myint_free_02231_gmpknd (gmpknd arg0) {
/* local vardec */
// ATSlocal_void (tmp21) ;
// ATSlocal_void (tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;

__ats_lab_myint_free_02231_gmpknd:
tmp23 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp22 = */ atslib_mpz_clear (tmp23) ;
tmp24 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp21 = */ atspre_ptr_free (tmp24) ;
return /* (tmp21) */ ;
} /* end of [myint_free_02231_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 3961(line=168, offs=3) -- 4079(line=173, offs=2)
*/
ATSstaticdec()
gmpknd
neg_myint_02233_gmpknd (gmpknd arg0) {
/* local vardec */
ATSlocal (gmpknd, tmp25) ;
// ATSlocal_void (tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;

__ats_lab_neg_myint_02233_gmpknd:
tmp27 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp26 = */ atslib_mpz_neg1 (tmp27) ;
tmp25 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp25) ;
} /* end of [neg_myint_02233_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 4163(line=179, offs=3) -- 4417(line=187, offs=2)
*/
ATSstaticdec()
gmpknd
neg1_myint_02234_gmpknd (gmpknd arg0) {
/* local vardec */
ATSlocal (gmpknd, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
// ATSlocal_void (tmp31) ;
// ATSlocal_void (tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;

__ats_lab_neg1_myint_02234_gmpknd:
tmp29 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp30 = ats_selsin_mac(tmp29, atslab_2) ;
/* tmp31 = */ atslib_mpz_init (tmp30) ;
tmp33 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp32 = */ atslib_mpz_neg2 (tmp30, tmp33) ;
tmp34 = tmp30 ;
tmp28 = ats_castfn_mac(gmpknd, tmp34) ;
return (tmp28) ;
} /* end of [neg1_myint_02234_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 4509(line=193, offs=3) -- 4734(line=199, offs=2)
*/
ATSstaticdec()
gmpknd
add01_myint_myint_02236_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp35) ;
// ATSlocal_void (tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;

__ats_lab_add01_myint_myint_02236_gmpknd:
tmp37 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp38 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp36 = */ atslib_mpz_add2_mpz (tmp37, tmp38) ;
tmp35 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp35) ;
} /* end of [add01_myint_myint_02236_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 4831(line=205, offs=3) -- 5056(line=211, offs=2)
*/
ATSstaticdec()
gmpknd
sub01_myint_myint_02237_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp39) ;
// ATSlocal_void (tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;

__ats_lab_sub01_myint_myint_02237_gmpknd:
tmp41 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp42 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp40 = */ atslib_mpz_sub2_mpz (tmp41, tmp42) ;
tmp39 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp39) ;
} /* end of [sub01_myint_myint_02237_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 5149(line=217, offs=3) -- 5278(line=222, offs=2)
*/
ATSstaticdec()
gmpknd
add_myint_int_02235_gmpknd (gmpknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp43) ;
// ATSlocal_void (tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;

__ats_lab_add_myint_int_02235_gmpknd:
tmp45 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp44 = */ atslib_mpz_add2_int (tmp45, arg1) ;
tmp43 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp43) ;
} /* end of [add_myint_int_02235_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 5373(line=228, offs=3) -- 5599(line=235, offs=2)
*/
ATSstaticdec()
gmpknd
mul01_myint_myint_02238_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp46) ;
// ATSlocal_void (tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;

__ats_lab_mul01_myint_myint_02238_gmpknd:
tmp48 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp49 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp47 = */ atslib_mpz_mul2_mpz (tmp48, tmp49) ;
tmp46 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp46) ;
} /* end of [mul01_myint_myint_02238_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 5677(line=239, offs=3) -- 6142(line=254, offs=2)
*/
ATSstaticdec()
gmpknd
mul10_myint_myint_02239_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp50) ;
ATSlocal (ats_ptr_type, tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
// ATSlocal_void (tmp53) ;
ATSlocal (ats_ptr_type, tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;

__ats_lab_mul10_myint_myint_02239_gmpknd:
tmp51 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg1)) ;
tmp52 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp51), atslab_2) ;
tmp54 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg1)) ;
tmp55 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp53 = */ atslib_mpz_mul3_mpz (tmp54, tmp55, tmp52) ;
tmp50 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg1)) ;
return (tmp50) ;
} /* end of [mul10_myint_myint_02239_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 6220(line=258, offs=3) -- 6574(line=268, offs=4)
*/
ATSstaticdec()
gmpknd
mul11_myint_myint_02240_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
ATSlocal (ats_ptr_type, tmp58) ;
// ATSlocal_void (tmp59) ;
// ATSlocal_void (tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
ATSlocal (ats_ptr_type, tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;

__ats_lab_mul11_myint_myint_02240_gmpknd:
tmp57 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp58 = ats_selsin_mac(tmp57, atslab_2) ;
/* tmp59 = */ atslib_mpz_init (tmp58) ;
tmp61 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp62 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp60 = */ atslib_mpz_mul3_mpz (tmp58, tmp61, tmp62) ;
tmp63 = tmp58 ;
tmp56 = ats_castfn_mac(gmpknd, tmp63) ;
return (tmp56) ;
} /* end of [mul11_myint_myint_02240_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 6673(line=274, offs=3) -- 7138(line=288, offs=2)
*/
ATSstaticdec()
gmpknd
div01_myint_myint_02241_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp64) ;
ATSlocal (ats_ptr_type, tmp65) ;
ATSlocal (ats_ptr_type, tmp66) ;
// ATSlocal_void (tmp67) ;
ATSlocal (ats_ptr_type, tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;

__ats_lab_div01_myint_myint_02241_gmpknd:
tmp65 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp66 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp65), atslab_2) ;
tmp68 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp69 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp67 = */ atslib_mpz_tdiv3_q_mpz (tmp66, tmp68, tmp69) ;
tmp64 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp64) ;
} /* end of [div01_myint_myint_02241_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 7238(line=294, offs=3) -- 7701(line=308, offs=2)
*/
ATSstaticdec()
gmpknd
ediv01_myint_myint_02243_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp70) ;
ATSlocal (ats_ptr_type, tmp71) ;
ATSlocal (ats_ptr_type, tmp72) ;
// ATSlocal_void (tmp73) ;
ATSlocal (ats_ptr_type, tmp74) ;
ATSlocal (ats_ptr_type, tmp75) ;

__ats_lab_ediv01_myint_myint_02243_gmpknd:
tmp71 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp72 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp71), atslab_2) ;
tmp74 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp75 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp73 = */ atslib_mpz_divexact3 (tmp72, tmp74, tmp75) ;
tmp70 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp70) ;
} /* end of [ediv01_myint_myint_02243_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 7801(line=314, offs=3) -- 8263(line=328, offs=2)
*/
ATSstaticdec()
gmpknd
mod01_myint_myint_02244_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp76) ;
ATSlocal (ats_ptr_type, tmp77) ;
ATSlocal (ats_ptr_type, tmp78) ;
// ATSlocal_void (tmp79) ;
ATSlocal (ats_ptr_type, tmp80) ;
ATSlocal (ats_ptr_type, tmp81) ;

__ats_lab_mod01_myint_myint_02244_gmpknd:
tmp77 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp78 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp77), atslab_2) ;
tmp80 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp81 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp79 = */ atslib_mpz_mod3_mpz (tmp78, tmp80, tmp81) ;
tmp76 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp76) ;
} /* end of [mod01_myint_myint_02244_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 8341(line=332, offs=3) -- 8695(line=342, offs=4)
*/
ATSstaticdec()
gmpknd
mod11_myint_myint_02245_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp82) ;
ATSlocal (ats_ptr_type, tmp83) ;
ATSlocal (ats_ptr_type, tmp84) ;
// ATSlocal_void (tmp85) ;
// ATSlocal_void (tmp86) ;
ATSlocal (ats_ptr_type, tmp87) ;
ATSlocal (ats_ptr_type, tmp88) ;
ATSlocal (ats_ptr_type, tmp89) ;

__ats_lab_mod11_myint_myint_02245_gmpknd:
tmp83 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp84 = ats_selsin_mac(tmp83, atslab_2) ;
/* tmp85 = */ atslib_mpz_init (tmp84) ;
tmp87 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp88 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp86 = */ atslib_mpz_mod3_mpz (tmp84, tmp87, tmp88) ;
tmp89 = tmp84 ;
tmp82 = ats_castfn_mac(gmpknd, tmp89) ;
return (tmp82) ;
} /* end of [mod11_myint_myint_02245_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 8794(line=348, offs=3) -- 9256(line=362, offs=2)
*/
ATSstaticdec()
gmpknd
gcd01_myint_myint_02246_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (gmpknd, tmp90) ;
ATSlocal (ats_ptr_type, tmp91) ;
ATSlocal (ats_ptr_type, tmp92) ;
// ATSlocal_void (tmp93) ;
ATSlocal (ats_ptr_type, tmp94) ;
ATSlocal (ats_ptr_type, tmp95) ;

__ats_lab_gcd01_myint_myint_02246_gmpknd:
tmp91 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp92 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp91), atslab_2) ;
tmp94 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp95 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp93 = */ atslib_mpz_gcd3_mpz (tmp92, tmp94, tmp95) ;
tmp90 = ats_castfn_mac(gmpknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp90) ;
} /* end of [gcd01_myint_myint_02246_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 9355(line=368, offs=3) -- 9509(line=374, offs=2)
*/
ATSstaticdec()
ats_int_type
compare_myint_int_02253_gmpknd (gmpknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp96) ;
ATSlocal (ats_ptr_type, tmp97) ;

__ats_lab_compare_myint_int_02253_gmpknd:
tmp97 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp96 = atslib_mpz_cmp_int (tmp97, arg1) ;
return (tmp96) ;
} /* end of [compare_myint_int_02253_gmpknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_gmp.dats: 9603(line=380, offs=3) -- 9841(line=386, offs=2)
*/
ATSstaticdec()
ats_int_type
compare_myint_myint_02258_gmpknd (gmpknd arg0, gmpknd arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp98) ;
ATSlocal (ats_ptr_type, tmp99) ;
ATSlocal (ats_ptr_type, tmp100) ;

__ats_lab_compare_myint_myint_02258_gmpknd:
tmp99 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp100 = ats_varget_mac(ats_ptr_type, arg1) ;
tmp98 = atslib_mpz_cmp_mpz (tmp99, tmp100) ;
return (tmp98) ;
} /* end of [compare_myint_myint_02258_gmpknd] */

/* static load function */

extern ats_void_type ATS_2d0_2e2_2e12_2libc_2SATS_2gmp_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__staload_flag = 1 ;

ATS_2d0_2e2_2e12_2libc_2SATS_2gmp_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
// extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__dynload () {
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_2edats__staload () ;

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

/* end of [pats_lintprgm_myint_dats.c] */
