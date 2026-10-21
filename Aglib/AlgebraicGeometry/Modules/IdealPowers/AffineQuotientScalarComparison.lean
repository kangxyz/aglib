/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientChartTower
public import Aglib.RingTheory.AdicCompletion.ScalarExtension

/-! # Agreement of chart-linear and structural-linear quotient sections -/

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

/-- Changing from the structural ideal to its extension does not change the
actual quotient section: both canonical comparisons retain original reduction. -/
theorem idealPowerQuotientAffineChartEquiv_mapIdeal (n : ℕ) :
    letI := idealSectionModule X α F U.val
    letI : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom A Γ(X, U) _
    ∀ x : Γ(F, U) ⧸ (I ^ n • ⊤ : Submodule A Γ(F, U)),
      idealPowerQuotientAffineChartEquiv f F I U n
          (AdicCompletion.mapIdealQuotientEquiv (S := Γ(X, U)) I Γ(F, U) n x) =
        idealQuotientAffineSectionsEquiv f F (I ^ n) U x := by
  let := idealSectionModule X α F U.val
  let : Algebra A Γ(X, U) := (idealSectionRingHom X α U.val).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom A Γ(X, U) _
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [AdicCompletion.mapIdealQuotientEquiv_mk,
    idealPowerQuotientAffineChartEquiv_mk, idealQuotientAffineSectionsEquiv_mk]

end AlgebraicGeometry.Scheme.Modules
