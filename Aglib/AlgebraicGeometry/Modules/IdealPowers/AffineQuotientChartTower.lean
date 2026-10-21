/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientChart
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTower
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # The original affine quotient tower over the chart ring -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) [F.IsQuasicoherent]
  (I : Ideal A) (U : X.affineOpens)

local notation "α" => idealThickeningBaseScalar f
local notation "J" => I.map (idealSectionRingHom X α U.val)

/-- The chart-linear quotient comparison for a power of the structural ideal. -/
def idealPowerQuotientAffineChartEquiv (n : ℕ) :
    (Γ(F, U) ⧸ (J ^ n • ⊤ : Submodule Γ(X, U) Γ(F, U))) ≃ₗ[Γ(X, U)]
      Γ(idealQuotient X α F (I ^ n), U) := by
  exact (Submodule.quotEquivOfEq _
    (idealQuotientAffineChartSubmodule f F (I ^ n) U) (by
      simp only [idealQuotientAffineChartSubmodule, Ideal.map_pow])).trans
        (idealQuotientAffineChartEquiv f F (I ^ n) U)

@[simp]
theorem idealPowerQuotientAffineChartEquiv_mk (n : ℕ) (x : Γ(F, U)) :
    idealPowerQuotientAffineChartEquiv f F I U n (Submodule.Quotient.mk x) =
      (idealQuotientπ X α F (I ^ n)).app U.val x := by
  simp only [idealPowerQuotientAffineChartEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, idealQuotientAffineChartEquiv_mk]

/-- Chart comparisons intertwine every original adic transition. -/
theorem idealPowerQuotientAffineChartEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : Γ(F, U) ⧸ (J ^ n • ⊤ : Submodule Γ(X, U) Γ(F, U))) :
    idealPowerQuotientAffineChartEquiv f F I U m (Submodule.factorPow J Γ(F, U) h x) =
      (idealPowerQuotientMap X α F I h).app U.val
        (idealPowerQuotientAffineChartEquiv f F I U n x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change idealPowerQuotientAffineChartEquiv f F I U m (Submodule.Quotient.mk x) = _
  simp only [idealPowerQuotientAffineChartEquiv_mk]
  exact (congrArg (fun k => k.app U.val x)
    (idealQuotientπ_map X α F (show I ^ n ≤ I ^ m from Ideal.pow_le_pow_right h))).symm

end AlgebraicGeometry.Scheme.Modules
