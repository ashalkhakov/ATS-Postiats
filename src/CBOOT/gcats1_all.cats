/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */
//
// Author: Hongwei Xi
// Authoremail: hwxi AT cs DOT bu DOT edu
// Start time: June 2008
//
/* ****** ****** */

/* include some .h files */
#ifndef _ATS_HEADER_NONE
#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"
#endif /* _ATS_HEADER_NONE */

/* ****** ****** */

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/array.cats"
#endif /* _ATS_PRELUDE_NONE */

/* ****** ****** */

#include "GCATS/gcats1.cats"
#include "GCATS/gcats1_top_dats.c"
#include "GCATS/gcats1_misc_dats.c"
#include "GCATS/gcats1_freeitmlst_dats.c"
#include "GCATS/gcats1_chunk_dats.c"
#include "GCATS/gcats1_globalentry_dats.c"
#include "GCATS/gcats1_marking_dats.c"
#include "GCATS/gcats1_collecting_dats.c"
#include "GCATS/gcats1_autops_dats.c"
#include "GCATS/gcats1_manops_dats.c"

/* ****** ****** */

ats_void_type
ATS_2d0_2e2_2e10_2ccomp_2runtime_2GCATS1_2gcats1_2esats__staload () {
static int ATS_2d0_2e2_2e10_2ccomp_2runtime_2GCATS1_2gcats1_2esats__staload_flag = 0 ;
if (ATS_2d0_2e2_2e10_2ccomp_2runtime_2GCATS1_2gcats1_2esats__staload_flag) return ;
ATS_2d0_2e2_2e10_2ccomp_2runtime_2GCATS1_2gcats1_2esats__staload_flag = 1 ;

return ;
} /* staload function */

/* ****** ****** */

/* end of [gcats1_all.cats] */
