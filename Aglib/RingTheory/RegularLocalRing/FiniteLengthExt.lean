/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.RegularSequence
public import Aglib.RingTheory.Support.FiniteLength
public import Mathlib.RingTheory.Depth.Rees

/-!
# Low-degree Ext vanishing for finite-length coefficients

For a regular local ring of dimension `d` and a finite-length module `N`, the
actual groups `Ext N R i` vanish for `i < d`. A regular system of parameters
and the native Rees theorem supply the proof. No depth, resolution, Ext
vanishing, or purity theorem is assumed.
-/

@[expose] public section

universe u

open CategoryTheory Abelian IsLocalRing
open scoped Pointwise

namespace IsRegularLocalRing

/-- A finite module supported at the closed point has no Ext into the regular
local ring below its dimension. -/
theorem subsingleton_ext_of_support_subset_closedPoint
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N]
    (hN : Module.support R N ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (i : ℕ) (hi : i < d) :
    Subsingleton (Ext N (ModuleCat.of R R) i) := by
  obtain ⟨rs, hlen, hreg, hspan⟩ := exists_regular_sequence_maximalIdeal R d hd
  apply ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) N hN
    (ModuleCat.of R R) ?_ rs ?_ hreg i (by simpa [hlen] using hi)
  · change maximalIdeal R • (⊤ : Submodule R R) < ⊤
    rw [smul_eq_mul, Ideal.mul_top]
    exact lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal R).ne_top
  · intro r hr
    rw [← hspan]
    exact Ideal.subset_span hr

/-- Finite-length coefficients have no Ext into a regular local ring in degrees
strictly smaller than its dimension. -/
theorem subsingleton_ext_of_isFiniteLength
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N)
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (i : ℕ) (hi : i < d) :
    Subsingleton (Ext N (ModuleCat.of R R) i) := by
  have hnoeth : IsNoetherian R N :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
  let : IsNoetherian R N := hnoeth
  exact subsingleton_ext_of_support_subset_closedPoint R N
    (Module.support_subset_closedPoint_of_isFiniteLength hN) d hd i hi

end IsRegularLocalRing
