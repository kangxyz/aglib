/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Algebraization.Detection
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
# Rank-one algebraization over a complete Noetherian base

An actual coherent module on a proper scheme is locally rank one if its
original pullbacks to all positive base-ideal thickenings are locally rank one.
No flatness of the scheme over the base is assumed. The residue fields are
arbitrary, and the adic ideal need not be maximal or even proper.

The proof commutes the original Fitting ideal sheaves with the original
geometric pullbacks. Proper coherent full faithfulness reflects the zero
and unit Fitting conditions, which give the required actual local bases.
Coherent effectivity alone is not used as a freeness assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Singleton local bases are precisely local bases of displayed rank one. -/
theorem isLocallyRankOne_iff_sheafHasRank_one {X : Scheme.{u}} (M : X.Modules) :
    IsLocallyRankOne X M ↔ SheafHasRank M 1 := by
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun i => ⟨(h i).some.trans (Equiv.ofUnique _ _)⟩⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun i => ⟨(h i).some.trans (Equiv.ofUnique _ _)⟩⟩

/-- A coherent module on a proper scheme over an adically complete
Noetherian ring is an actual line bundle when every positive original
geometric reduction is a line bundle. Neither base flatness nor restrictions
on residue fields are required. -/
theorem isLocallyRankOne_of_proper_positiveThickening
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hred : ∀ n : ℕ, 0 < n →
      IsLocallyRankOne (idealThickeningSpace f (I ^ n))
        ((pullback (idealThickeningι f (I ^ n))).obj M)) :
    IsLocallyRankOne X M := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : M.IsFinitePresentation := QuasiCoherent.affineLocallyFiniteType_finitePresentation hM
  have hfit (n : ℕ) (hn : 0 < n) :
      (fittingIdealSheaf M hM 0).comap (idealThickeningι f (I ^ n)) = ⊥ ∧
      (fittingIdealSheaf M hM 1).comap (idealThickeningι f (I ^ n)) = ⊤ := by
    let i := idealThickeningι f (I ^ n)
    have hN := QuasiCoherent.affineLocallyFiniteType_pullback i hM
    have hr := (isLocallyRankOne_iff_sheafHasRank_one _).mp (hred n hn)
    have hh := fittingIdealSheaf_eq_of_sheafHasRank ((pullback i).obj M) hN hr
    rw [fittingIdealSheaf_comap i M hM hN 0, fittingIdealSheaf_comap i M hM hN 1]
    exact ⟨hh.1 0 (by decide), hh.2⟩
  have h0 : fittingIdealSheaf M hM 0 = ⊥ :=
    idealSheaf_eq_bot_of_positiveThickening_comap_eq_bot I f _ (fun n hn => (hfit n hn).1)
  have h1 : fittingIdealSheaf M hM 1 = ⊤ :=
    idealSheaf_eq_top_of_positiveThickening_comap_eq_top I f _ (fun n hn => (hfit n hn).2)
  apply (isLocallyRankOne_iff_sheafHasRank_one M).mpr
  apply (fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank M hM 1).mp
  refine ⟨?_, h1⟩
  intro k hk
  have : k = 0 := by omega
  simpa only [this] using h0

/-- The actual line bundle supplied by the all-order geometric criterion.
Its underlying module is literally the given coherent module. -/
def lineBundleOfProperPositiveThickening
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hred : ∀ n : ℕ, 0 < n →
      IsLocallyRankOne (idealThickeningSpace f (I ^ n))
        ((pullback (idealThickeningι f (I ^ n))).obj M)) : LineBundle X :=
  ⟨M, isLocallyRankOne_of_proper_positiveThickening I f M hM hred⟩

/-- Complete-local specialization for the actual powers of the maximal ideal. -/
theorem isLocallyRankOne_of_proper_maximalIdealThickening
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hred : ∀ n : ℕ, 0 < n →
      IsLocallyRankOne (idealThickeningSpace f (IsLocalRing.maximalIdeal R ^ n))
        ((pullback (idealThickeningι f (IsLocalRing.maximalIdeal R ^ n))).obj M)) :
    IsLocallyRankOne X M :=
  isLocallyRankOne_of_proper_positiveThickening (IsLocalRing.maximalIdeal R) f M hM hred

end AlgebraicGeometry.Scheme.Modules.Invertible
