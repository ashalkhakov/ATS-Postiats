/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-5-22:  9h:53m
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

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_hidexp_loc ;
ats_ptr_type atslab_hidexp_type ;
ats_ptr_type atslab_hidexp_node ;
} anairiats_rec_0 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_1 ;

typedef struct {
ats_int_type atslab_0 ;
} anairiats_sum_2 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_3 ;

typedef struct {
ats_ptr_type atslab_0 ;
} anairiats_sum_4 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_5 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_6 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__None_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__Some_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__FUNCLOclo_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__HDEdelay_48) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__HDEldelay_49) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__HDElazyeval_50) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__d2var_make_any) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__d2var_inc_utimes) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__hisexp_bool_t0ype) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__hisexp_fun) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hipat_var) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_var) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_ignore) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_if) (ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_make_type) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_tmpknd) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_funent) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__the_funlablst_add) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_lamfix) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_make_funlab) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_funlab) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_move_delay) (ats_ptr_type, ats_ptr_type, ats_int_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_move_lazyeval) (ats_ptr_type, ats_ptr_type, ats_int_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instrseq_add) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_get_tmplevel) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_dec_tailcalenv) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_inc_tailcalenv) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_add_flabsetenv) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_funlab_arg_body) (ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type, ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 1670(line=55, offs=3) -- 2761(line=100, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_delay (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_ptr_type, tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;
ATSlocal (ats_ptr_type, tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
// ATSlocal_void (tmp10) ;
// ATSlocal_void (tmp11) ;
// ATSlocal_void (tmp12) ;
ATSlocal (ats_int_type, tmp13) ;
// ATSlocal_void (tmp14) ;
ATSlocal (ats_bool_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;
// ATSlocal_void (tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
// ATSlocal_void (tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_delay:
tmp1 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_loc) ;
tmp2 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_node) ;
if (((ats_sum_ptr_type)tmp2)->tag != 48) { ats_caseof_failure_handle ("/home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 1735(line=58, offs=5) -- 1768(line=58, offs=38)") ; }
tmp3 = ats_caselptrlab_mac(anairiats_sum_1, tmp2, atslab_0) ;
tmp4 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, tmp3), atslab_hidexp_type) ;
tmp6 = ATS_MALLOC(sizeof(anairiats_sum_2)) ;
ats_selptrset_mac(anairiats_sum_2, tmp6, atslab_0, -1) ;
tmp7 = (ats_sum_ptr_type)0 ;
tmp5 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__hisexp_fun (tmp6, tmp7, tmp4) ;
tmp8 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_make_type (tmp5) ;
tmp9 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_make_funlab (tmp1, tmp8) ;
/* tmp10 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__the_funlablst_add (tmp8) ;
/* tmp11 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_add_flabsetenv (arg0, tmp8) ;
/* tmp12 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_inc_tailcalenv (arg0, tmp8) ;
tmp13 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_get_tmplevel (arg0) ;
tmp15 = atspre_gt_int_int (tmp13, 0) ;
if (tmp15) {
/* tmp14 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_tmpknd (tmp8, 1) ;
} else {
/* empty */
} /* end of [if] */
tmp16 = (ats_sum_ptr_type)0 ;
tmp17 = (ats_sum_ptr_type)0 ;
tmp18 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_funlab (tmp1, tmp8) ;
tmp20 = (ats_sum_ptr_type)0 ;
tmp19 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp19, atslab_0, tmp18) ;
ats_selptrset_mac(anairiats_sum_3, tmp19, atslab_1, tmp20) ;
tmp22 = (ats_sum_ptr_type)0 ;
tmp21 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_funlab_arg_body (arg0, tmp8, tmp16, tmp17, tmp19, tmp1, tmp22, tmp3) ;
tmp24 = ATS_MALLOC(sizeof(anairiats_sum_4)) ;
ats_selptrset_mac(anairiats_sum_4, tmp24, atslab_0, tmp21) ;
/* tmp23 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_funent (tmp8, tmp24) ;
/* tmp25 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_dec_tailcalenv (arg0) ;
tmp27 = (ats_sum_ptr_type)0 ;
tmp26 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_lamfix (tmp27, tmp9) ;
tmp28 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_move_delay (tmp1, arg2, 0, tmp4, tmp26) ;
/* tmp0 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instrseq_add (arg1, tmp28) ;
return /* (tmp0) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_delay] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 2855(line=106, offs=3) -- 4415(line=162, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_ldelay (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3) {
/* local vardec */
// ATSlocal_void (tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_ptr_type, tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
// ATSlocal_void (tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;
ATSlocal (ats_ptr_type, tmp50) ;
// ATSlocal_void (tmp51) ;
// ATSlocal_void (tmp52) ;
// ATSlocal_void (tmp53) ;
ATSlocal (ats_int_type, tmp54) ;
// ATSlocal_void (tmp55) ;
ATSlocal (ats_bool_type, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
ATSlocal (ats_ptr_type, tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
ATSlocal (ats_ptr_type, tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
ATSlocal (ats_ptr_type, tmp62) ;
// ATSlocal_void (tmp63) ;
ATSlocal (ats_ptr_type, tmp64) ;
// ATSlocal_void (tmp65) ;
ATSlocal (ats_ptr_type, tmp66) ;
ATSlocal (ats_ptr_type, tmp67) ;
ATSlocal (ats_ptr_type, tmp68) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_ldelay:
tmp30 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_loc) ;
tmp31 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_node) ;
if (((ats_sum_ptr_type)tmp31)->tag != 49) { ats_caseof_failure_handle ("/home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 2920(line=109, offs=5) -- 2961(line=109, offs=46)") ; }
tmp32 = ats_caselptrlab_mac(anairiats_sum_5, tmp31, atslab_0) ;
tmp33 = ats_caselptrlab_mac(anairiats_sum_5, tmp31, atslab_1) ;
tmp34 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, tmp32), atslab_hidexp_type) ;
tmp35 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__hisexp_bool_t0ype () ;
tmp37 = (ats_sum_ptr_type)0 ;
tmp36 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp36, atslab_0, tmp35) ;
ats_selptrset_mac(anairiats_sum_3, tmp36, atslab_1, tmp37) ;
tmp39 = ATS_MALLOC(sizeof(anairiats_sum_2)) ;
ats_selptrset_mac(anairiats_sum_2, tmp39, atslab_0, 1) ;
tmp38 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__hisexp_fun (tmp39, tmp36, tmp34) ;
tmp40 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_make_type (tmp38) ;
tmp41 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_make_funlab (tmp30, tmp40) ;
tmp42 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__d2var_make_any (tmp30) ;
/* tmp43 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__d2var_inc_utimes (tmp42) ;
tmp44 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_var (tmp30, tmp35, tmp42) ;
tmp46 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, tmp33), atslab_hidexp_loc) ;
tmp45 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_ignore (tmp46, tmp34, tmp33) ;
tmp47 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hidexp_if (tmp30, tmp34, tmp44, tmp32, tmp45) ;
tmp48 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__hipat_var (tmp30, tmp35, tmp42) ;
tmp50 = (ats_sum_ptr_type)0 ;
tmp49 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp49, atslab_0, tmp48) ;
ats_selptrset_mac(anairiats_sum_3, tmp49, atslab_1, tmp50) ;
/* tmp51 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__the_funlablst_add (tmp40) ;
/* tmp52 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_add_flabsetenv (arg0, tmp40) ;
/* tmp53 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_inc_tailcalenv (arg0, tmp40) ;
tmp54 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_get_tmplevel (arg0) ;
tmp56 = atspre_gt_int_int (tmp54, 0) ;
if (tmp56) {
/* tmp55 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_tmpknd (tmp40, 1) ;
} else {
/* empty */
} /* end of [if] */
tmp57 = (ats_sum_ptr_type)0 ;
tmp58 = (ats_sum_ptr_type)0 ;
tmp59 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_funlab (tmp30, tmp40) ;
tmp61 = (ats_sum_ptr_type)0 ;
tmp60 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp60, atslab_0, tmp59) ;
ats_selptrset_mac(anairiats_sum_3, tmp60, atslab_1, tmp61) ;
tmp62 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_funlab_arg_body (arg0, tmp40, tmp57, tmp58, tmp60, tmp30, tmp49, tmp47) ;
tmp64 = ATS_MALLOC(sizeof(anairiats_sum_4)) ;
ats_selptrset_mac(anairiats_sum_4, tmp64, atslab_0, tmp62) ;
/* tmp63 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__funlab_set_funent (tmp40, tmp64) ;
/* tmp65 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__ccompenv_dec_tailcalenv (arg0) ;
tmp67 = (ats_sum_ptr_type)0 ;
tmp66 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__primval_lamfix (tmp67, tmp41) ;
tmp68 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_move_delay (tmp30, arg2, 1, tmp34, tmp66) ;
/* tmp29 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instrseq_add (arg1, tmp68) ;
return /* (tmp29) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_ldelay] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 4510(line=168, offs=3) -- 4831(line=180, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_lazyeval (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3) {
/* local vardec */
// ATSlocal_void (tmp69) ;
ATSlocal (ats_ptr_type, tmp70) ;
ATSlocal (ats_ptr_type, tmp71) ;
ATSlocal (ats_ptr_type, tmp72) ;
ATSlocal (ats_int_type, tmp73) ;
ATSlocal (ats_ptr_type, tmp74) ;
ATSlocal (ats_ptr_type, tmp75) ;
ATSlocal (ats_ptr_type, tmp76) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_lazyeval:
tmp70 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_loc) ;
tmp71 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_type) ;
tmp72 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg3), atslab_hidexp_node) ;
if (((ats_sum_ptr_type)tmp72)->tag != 50) { ats_caseof_failure_handle ("/home/hwxi/Research/ATS-Postiats/src/pats_ccomp_lazyeval.dats: 4603(line=172, offs=5) -- 4649(line=172, offs=51)") ; }
tmp73 = ats_caselptrlab_mac(anairiats_sum_6, tmp72, atslab_0) ;
tmp74 = ats_caselptrlab_mac(anairiats_sum_6, tmp72, atslab_1) ;
tmp75 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp (arg0, arg1, tmp74) ;
tmp76 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instr_move_lazyeval (tmp70, arg2, tmp73, tmp71, tmp75) ;
/* tmp69 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__instrseq_add (arg1, tmp76) ;
return /* (tmp69) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__hidexp_ccomp_ret_lazyeval] */

/* static load function */

extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__staload_flag = 1 ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_dynexp2_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_histaexp_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_hidynexp_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_ccomp_lazyeval_2edats__staload () ;

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

/* end of [pats_ccomp_lazyeval_dats.c] */
