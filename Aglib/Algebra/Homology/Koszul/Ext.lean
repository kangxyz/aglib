/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Resolution
public import Aglib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Native Ext bounds from the original finite Koszul resolution

A weakly regular finite list gives its actual ideal quotient a projective
dimension at most the list length. The same supplied Koszul resolution
kills every native Ext class above that length, for arbitrary coefficient
modules and any supported Ext universe. No Noetherian or finiteness
hypothesis is needed on the ring or coefficient. Lower-degree purity and
the determinant-normalized top class are separate calculations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The actual quotient by a weakly regular list has the native projective
dimension bound, witnessed by the original finite Koszul resolution. -/
theorem quotient_hasProjectiveDimensionLE_of_weaklyRegular (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList s)) s.length :=
  (finiteProjectiveResolution s hs).hasProjectiveDimensionLE_of_isZero_X s.length
    (fun i hi => isZero_X s i hi)

/-- Every original Ext class vanishes above the actual regular-list length,
with arbitrary coefficients and without changing the Ext universe. -/
theorem ext_eq_zero_above_length [HasExt.{w} (ModuleCat.{u} R)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) (n : ℕ) (hn : s.length < n)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.ofList s)) N n) : e = 0 :=
  (finiteProjectiveResolution s hs).ext_eq_zero_of_isZero_X n (isZero_X s n hn) e

end ChainComplex.Koszul
