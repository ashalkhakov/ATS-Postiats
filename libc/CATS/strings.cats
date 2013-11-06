/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/***********************************************************************/

/* (*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
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
*) */

/* ****** ****** */

/*
** Source:
** $PATSHOME/libc/CATS/CODEGEN/strings.atxt
** Time of generation: Fri Nov  1 21:34:14 2013
*/

/* ****** ****** */

/*
(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: February, 2013 *)
*/

/* ****** ****** */

#ifndef ATSLIB_LIBC_STRINGS_CATS
#define ATSLIB_LIBC_STRINGS_CATS

/* ****** ****** */

#include <strings.h>

/* ****** ****** */

#define atslib_index_int index
#define atslib_index_char(c) index((int)c)

#define atslib_rindex_int rindex
#define atslib_rindex_char(c) rindex((int)c)

/* ****** ****** */

#define atslib_strcasecmp strcasecmp
#define atslib_strncasecmp strncasecmp

/* ****** ****** */

#endif // ifndef ATSLIB_LIBC_STRINGS_CATS

/* ****** ****** */

/* end of [strings.cats] */
