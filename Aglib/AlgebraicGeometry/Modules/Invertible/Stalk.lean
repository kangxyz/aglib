/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.Stalk
public import Aglib.AlgebraicGeometry.Modules.FittingIdeal.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.Invertible.RankOne
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine

/-!
# Original stalk frames and locally rank-one sheaves

A finitely presented module sheaf is locally rank one exactly when each
original stalk has a linear frame over its actual local ring. Fitting
ideals turn the pointwise frames into genuine finite local bases. The
converse uses the original pullback to the local spectrum and needs no
finiteness hypothesis. No global trivialization is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} (M : X.Modules)

/-- A locally rank-one sheaf has a frame at every original stalk. This
direction does not require a separate finite-presentation hypothesis. -/
theorem nonempty_stalkLinearEquiv_of_isLocallyRankOne
    (hM : IsLocallyRankOne X M) (x : X) :
    Nonempty (((moduleStalk X x).obj M) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  let A : CommRingCat.{u} := X.presheaf.stalk x
  let L : LineBundle (Spec A) :=
    ⟨(pullback (X.fromSpecStalk x)).obj M, pullback_locallyRankOne _ _ hM⟩
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing A L
  let E : (moduleStalk X x).obj M ≅ ModuleCat.of A A :=
    stalkFromSpecStalkSectionsIso X x M ≪≫ moduleSpecΓFunctor.mapIso e ≪≫
      globalSectionsUnitIso
  exact ⟨E.toLinearEquiv⟩

/-- Actual frames at every original stalk give local rank one for a finitely
presented sheaf, through its actual Fitting ideal sheaves. -/
theorem isLocallyRankOne_of_stalkLinearEquiv [M.IsFinitePresentation]
    (h : ∀ x : X, Nonempty (((moduleStalk X x).obj M) ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x)) : IsLocallyRankOne X M := by
  have hM := QuasiCoherent.affineLocallyFiniteType_of_finitePresentation M
  apply (isLocallyRankOne_iff_sheafHasRank_one M).mpr
  apply (fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank M hM 1).mp
  have hfit (x : X) (k : ℕ) : (fittingIdealSheaf M hM k).stalkIdeal x =
      if 1 ≤ k then ⊤ else ⊥ := by
    obtain ⟨e⟩ := h x
    rw [fittingIdealSheaf_stalkIdeal M hM k x, Module.fittingIdeal_congr e k]
    simpa using Module.fittingIdeal_of_basis
      (Module.Basis.singleton PUnit.{u + 1} (X.presheaf.stalk x)) k
  constructor
  · intro k hk
    apply IdealSheafData.ext_stalkIdeal
    intro x
    rw [hfit, ite_eq_right (Nat.not_le_of_lt hk)]
    simp [IdealSheafData.stalkIdeal]
  · apply IdealSheafData.ext_stalkIdeal
    intro x
    rw [hfit, ite_eq_left (le_refl 1), IdealSheafData.stalkIdeal_top]

/-- A finitely presented sheaf is locally rank one if and only if every
original module stalk is linearly isomorphic to its original local ring. -/
theorem isLocallyRankOne_iff_stalkLinearEquiv [M.IsFinitePresentation] :
    IsLocallyRankOne X M ↔ ∀ x : X, Nonempty (((moduleStalk X x).obj M) ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x) :=
  ⟨fun h x => nonempty_stalkLinearEquiv_of_isLocallyRankOne M h x,
    isLocallyRankOne_of_stalkLinearEquiv M⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
