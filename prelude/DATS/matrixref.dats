(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2013 Hongwei Xi, ATS Trustful Software, Inc.
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
*)

(* ****** ****** *)

(*
** Source:
** $PATSHOME/prelude/DATS/CODEGEN/matrixref.atxt
** Time of generation: Thu Jan 16 16:37:28 2014
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: Feburary, 2012 *)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

implement{a}
matrixref_make_elt
  (nrow, ncol, x) =
  matrixptr_refize(matrixptr_make_elt<a> (nrow, ncol, x))
// end of [matrixref_make_elt]

(* ****** ****** *)

implement{a}
matrixref_get_at_size
  (A, i, n, j) = let
//
val
(
vbox pf | p
) = matrixref_get_viewptr (A)
//
in
  matrix_get_at_size (!p, i, n, j)
end // end of [matrixref_get_at_size]

(* ****** ****** *)

implement{a}
matrixref_set_at_size
  (A, i, n, j, x) = let
//
val
(
vbox pf | p
) = matrixref_get_viewptr (A)
//
in
  matrix_set_at_size (!p, i, n, j, x)
end // end of [matrixref_set_at_size]

(* ****** ****** *)

implement{a}
matrixref_tabulate
  (nrow, ncol) =
  matrixptr_refize (matrixptr_tabulate<a> (nrow, ncol))
// end of [matrixref_tabulate]

(* ****** ****** *)

local

datatype
mtrxszref
(
  a:viewt@ype
) =
  {m,n:int}
  MTRXSZREF of
  (
    matrixref (a, m, n), size_t (m), size_t (n)
  )
// end of [mtrxszref]

assume
mtrxszref_vt0ype_type = mtrxszref

in (* in of [local] *)

implement{}
mtrxszref_make_matrixref
  (M, nrow, ncol) = MTRXSZREF (M, nrow, ncol)
// end of [mtrxszref_make_matrixref]

(* ****** ****** *)

implement{}
mtrxszref_get_ref (MSZ) = let
  val+MTRXSZREF (M, nrow, ncol) = MSZ in $UN.cast2Ptr1(M)
end // end of [mtrxszref_get_ref]

(* ****** ****** *)

implement{}
mtrxszref_get_nrow (MSZ) = let
  val+MTRXSZREF (M, nrow, ncol) = MSZ in nrow
end // end of [mtrxszref_get_nrow]

implement{}
mtrxszref_get_ncol (MSZ) = let
  val+MTRXSZREF (M, nrow, ncol) = MSZ in ncol
end // end of [mtrxszref_get_ncol]

(* ****** ****** *)

implement{}
mtrxszref_get_refsize
   (MSZ, nrow_r, ncol_r) = let
//
val+MTRXSZREF (M, nrow, ncol) = MSZ
prval ((*void*)) = lemma_matrixref_param (M)
//
in
  nrow_r := nrow; ncol_r := ncol; M(*matrixref*)
end // end of [mtrxszref_get_nrow]

end // end of [local]

(* ****** ****** *)

implement{a}
mtrxszref_make_elt
  (nrow, ncol, x) = let
  val nrow = g1ofg0_uint (nrow)
  val ncol = g1ofg0_uint (ncol)
  val M = matrixref_make_elt<a> (nrow, ncol, x)
in
  mtrxszref_make_matrixref (M, nrow, ncol)
end // end of [mtrxszref_make_elt]

(* ****** ****** *)

implement{a}
mtrxszref_get_at_size
  (MSZ, i, j) = $effmask_wrt let
//
var nrow: size_t
and ncol: size_t
val M = mtrxszref_get_refsize (MSZ, nrow, ncol)
val i = g1ofg0_uint (i)
val j = g1ofg0_uint (j)
//
in
//
if nrow > i then (
  if ncol > j then
    matrixref_get_at_size (M, i, ncol, j)
  else $raise ArraySubscriptExn((*void*))
) else $raise ArraySubscriptExn((*void*))
//
end // end of [mtrxszref_get_at_size]

implement
{a}{tk}
mtrxszref_get_at_gint
  (ASZ, i, j) = let
in
//
if i >= 0 then
if j >= 0 then
  mtrxszref_get_at_size (ASZ, g0i2u(i), g0i2u(j))
else $raise ArraySubscriptExn((* j < 0 *))
else $raise ArraySubscriptExn((* i < 0 *))
//
end // end of [mtrxszref_get_at_gint]

implement
{a}{tk}
mtrxszref_get_at_guint
  (ASZ, i, j) = let
in
//
mtrxszref_get_at_size (ASZ, g0u2u(i), g0u2u(j))
//
end // end of [mtrxszref_get_at_gint]

(* ****** ****** *)

implement{a}
mtrxszref_set_at_size
  (MSZ, i, j, x) = $effmask_wrt let
//
var nrow: size_t
and ncol: size_t
val M = mtrxszref_get_refsize (MSZ, nrow, ncol)
val i = g1ofg0_uint (i)
val j = g1ofg0_uint (j)
//
in
//
if nrow > i then (
  if ncol > j then
    matrixref_set_at_size (M, i, ncol, j, x)
  else $raise ArraySubscriptExn((*void*))
) else $raise ArraySubscriptExn((*void*))
//
end // end of [mtrxszref_set_at_size]

implement
{a}{tk}
mtrxszref_set_at_gint
  (ASZ, i, j, x) = let
in
//
if i >= 0 then
if j >= 0 then
  mtrxszref_set_at_size (ASZ, g0i2u(i), g0i2u(j), x)
else $raise ArraySubscriptExn((* j < 0 *))
else $raise ArraySubscriptExn((* i < 0 *))
//
end // end of [mtrxszref_set_at_gint]

implement
{a}{tk}
mtrxszref_set_at_guint
  (ASZ, i, j, x) = let
in
//
mtrxszref_set_at_size (ASZ, g0u2u(i), g0u2u(j), x)
//
end // end of [mtrxszref_set_at_gint]

(* ****** ****** *)

implement{a}
mtrxszref_tabulate
  (nrow, ncol) = let
  val nrow = g1ofg0_uint (nrow)
  val ncol = g1ofg0_uint (ncol)
  val M =
    matrixref_tabulate<a> (nrow, ncol)
  // end of [val]
in 
  mtrxszref_make_matrixref (M, nrow, ncol)
end // end of [mtrxszref_tabulate]

(* ****** ****** *)

(* end of [matrixref.dats] *)
