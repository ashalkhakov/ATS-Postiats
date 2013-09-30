(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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
*)

(* ****** ****** *)

(*
** Source:
** $PATSHOME/prelude/SATS/CODEGEN/matrixref.atxt
** Time of generation: Mon Sep 30 01:01:39 2013
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: April, 2013 *)

(* ****** ****** *)

#define NSH (x) x // for commenting: no sharing
#define SHR (x) x // for commenting: it is shared

(* ****** ****** *)

sortdef tk = tkind

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)
//
// matrixref: reference to a matrix with no dimension info attached
//
(* ****** ****** *)

abstype
matrixref_vt0ype_int_int_type
  (a:vt@ype(*invariant*), nrow: int, ncol:int) = ptr
stadef matrixref = matrixref_vt0ype_int_int_type

(* ****** ****** *)

praxi
lemma_matrixref_param
  {a:vt0p}{m,n:int} (A: matrixref (a, m, n)): [m >= 0; n >= 0] void
// end of [lemma_matrixref_param]

(* ****** ****** *)

castfn
matrixptr_refize
  {a:vt0p}
  {l:addr}
  {m,n:int} (
  A: matrixptr (INV(a), l, m, n)
) :<!wrt> matrixref (a, m, n) // end of [matrixptr_refize]

castfn
matrixref_get_viewptr
  {a:vt0p}
  {m,n:int} (
  A: matrixref (a, m, n)
) :<> [l:addr] (vbox (matrix_v (a, l, m, n)) | ptr l)

(* ****** ****** *)

fun{
a:t0p
} matrixref_make_elt{m,n:int}
  (m: size_t m, n: size_t n, x: a):<!wrt> matrixref (a, m, n)
// end of [matrixref_make_elt]

(* ****** ****** *)

fun{a:t0p}
matrixref_get_at_int{m,n:int}
(
  A: matrixref (a, m, n), i: natLt(m), n: int(n), j: natLt(n)
) :<!ref> (a) // end of [matrixref_get_at_int]
overload [] with matrixref_get_at_int

fun{a:t0p}
matrixref_get_at_size{m,n:int}
(
  A: matrixref (a, m, n), i: sizeLt(m), n: size_t(n), j: sizeLt(n)
) :<!ref> (a) // end of [matrixref_get_at_size]
overload [] with matrixref_get_at_size
//
symintr matrixref_get_at
overload matrixref_get_at with matrixref_get_at_int of 0
overload matrixref_get_at with matrixref_get_at_size of 0
//
(* ****** ****** *)

fun{a:t0p}
matrixref_set_at_int
  {m,n:int}
(
  A: matrixref (INV(a), m, n), i: natLt (m), n: int n, j: natLt (n), x: a
) :<!refwrt> void // end of [matrixref_set_at_int]
overload [] with matrixref_set_at_int

fun{a:t0p}
matrixref_set_at_size
  {m,n:int}
(
  A: matrixref (INV(a), m, n), i: sizeLt (m), n: size_t n, j: sizeLt (n), x: a
) :<!refwrt> void // end of [matrixref_set_at_size]
overload [] with matrixref_set_at_size

symintr matrixref_set_at
overload matrixref_set_at with matrixref_set_at_int of 0
overload matrixref_set_at with matrixref_set_at_size of 0

(* ****** ****** *)

fun{a:vt0p}
matrixref_exch_at_int
  {m,n:int}
(
  A: matrixref (INV(a), m, n)
, i: natLt (m), n: int n, j: natLt (n), x: &a >> _
) :<!refwrt> void // end of [matrixref_exch_at_int]

fun{a:vt0p}
matrixref_exch_at_size
  {m,n:int}
(
  A: matrixref (INV(a), m, n)
, i: sizeLt (m), n: size_t n, j: sizeLt (n), x: &a >> _
) :<!refwrt> void // end of [matrixref_exch_at_size]

symintr matrixref_exch_at
overload matrixref_exch_at with matrixref_exch_at_int of 0
overload matrixref_exch_at with matrixref_exch_at_size of 0

(* ****** ****** *)
(*
fun{a:vt0p}
matrix_tabulate$fopr (i: size_t, j: size_t): (a)
*)
fun{a:vt0p}
matrixref_tabulate
  {m,n:int} (nrow: size_t m, ncol: size_t n): matrixref (a, m, n)
//
(* ****** ****** *)
//
// mtrxszref: a reference to a matrix with size information attached
//
(* ****** ****** *)

abstype // in-variant
mtrxszref_vt0ype_type (a: vt@ype) = ptr
stadef mtrxszref = mtrxszref_vt0ype_type

(* ****** ****** *)

fun{}
mtrxszref_make_matrixref
  {a:vt0p}{m,n:int}
(
  M: matrixref (a, m, n), m: size_t m, n: size_t n
) :<!wrt> mtrxszref (a) // endfun

(* ****** ****** *)

fun{
} mtrxszref_get_ref{a:vt0p} (M: mtrxszref (a)):<> Ptr1
fun{
} mtrxszref_get_nrow{a:vt0p} (M: mtrxszref (a)):<> size_t
fun{
} mtrxszref_get_ncol{a:vt0p} (M: mtrxszref (a)):<> size_t

(* ****** ****** *)

symintr .ref .nrow .ncol
overload .ref with mtrxszref_get_ref
overload .nrow with mtrxszref_get_nrow
overload .ncol with mtrxszref_get_ncol

(* ****** ****** *)

fun{}
mtrxszref_get_refsize{a:vt0p}
(
  M: mtrxszref (a)
, nrol: &size_t? >> size_t m, ncol: &size_t? >> size_t (n)
) :<!wrt> #[m,n:nat] matrixref (a, m, n) // endfun

(* ****** ****** *)

fun{a:t0p}
mtrxszref_make_elt
  (nrow: size_t, ncol: size_t, init: a):<!wrt> mtrxszref (a)
// end of [mtrxszref_make_elt]

(* ****** ****** *)

fun{a:t0p}
mtrxszref_get_at_size
  (M: mtrxszref(a), i: size_t, j: size_t):<!exnref> a
fun{
a:t0p}{tk:tk
} mtrxszref_get_at_gint
  (M: mtrxszref(a), i: g0int(tk), j: g0int(tk)):<!exnref> a
overload [] with mtrxszref_get_at_gint of 0
fun{
a:t0p}{tk:tk
} mtrxszref_get_at_guint
  (M: mtrxszref(a), i: g0uint(tk), j: g0uint(tk)):<!exnref> a
overload [] with mtrxszref_get_at_guint of 0

(* ****** ****** *)

fun{a:t0p}
mtrxszref_set_at_size
  (M: mtrxszref(a), i: size_t, j: size_t, x: a):<!exnref> void
fun{
a:t0p}{tk:tk
} mtrxszref_set_at_gint
  (M: mtrxszref(a), i: g0int(tk), j: g0int(tk), x: a):<!exnref> void
overload [] with mtrxszref_set_at_gint of 0
fun{
a:t0p}{tk:tk
} mtrxszref_set_at_guint
  (M: mtrxszref(a), i: g0uint(tk), j: g0uint(tk), x: a):<!exnref> void
overload [] with mtrxszref_set_at_guint of 0

(* ****** ****** *)

(*
fun{a:vt0p}
matrix_tabulate$fopr (i: size_t, j: size_t): (a)
*)
fun{a:vt0p}
mtrxszref_tabulate (nrow: size_t, ncol: size_t): mtrxszref (a)
//
(* ****** ****** *)

(* end of [matrixref.sats] *)
