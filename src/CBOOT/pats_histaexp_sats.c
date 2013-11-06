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

/* prologues from statically loaded files */

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

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
ats_ptr_type atslab_hisexp_name ;
ats_ptr_type atslab_hisexp_node ;
} anairiats_rec_0 ;

/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HITNAM_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSLABELED_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtybox_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyabs_1) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEfun_2) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcfun_3) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcst_4) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEapp_5) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEextype_6) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSErefarg_7) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyarr_8) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrec_9) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrecsin_10) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtysum_11) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyvar_12) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEvararg_13) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEs2exp_14) ;

/* exn constructor declarations */
/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_util_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_util_2esats__staload () ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HITNAM_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSLABELED_0.tag = 0 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtybox_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyabs_1.tag = 1 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEfun_2.tag = 2 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcfun_3.tag = 3 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcst_4.tag = 4 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEapp_5.tag = 5 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEextype_6.tag = 6 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSErefarg_7.tag = 7 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyarr_8.tag = 8 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrec_9.tag = 9 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrecsin_10.tag = 10 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtysum_11.tag = 11 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyvar_12.tag = 12 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEvararg_13.tag = 13 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEs2exp_14.tag = 14 ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_histaexp_sats.c] */
