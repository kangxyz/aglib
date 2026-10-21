/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Scalars

/-! # Zero and unit ideal boundary cases of actual coefficient quotients -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- The unit-ideal coefficient inclusion is the canonical isomorphism with `F`. -/
theorem idealMultipleι_top_isIso : IsIso (idealMultipleι X α F ⊤) := by
  let : IsSplitEpi (idealMultipleι X α F ⊤) := IsSplitEpi.mk'
    { section_ := idealMultipleScalar X α F ⊤ ⟨1, trivial⟩
      id := by simp [globalScalarEndomorphism] }
  exact isIso_of_mono_of_isSplitEpi _

/-- The zeroth power coefficient is canonically the original coefficient. -/
def idealPowerZeroIso (I : Ideal A) : idealPower X α F I 0 ≅ F := by
  have h : IsIso (idealMultipleι X α F (I ^ 0)) := by
    have hpow : I ^ 0 = (⊤ : Ideal A) := by simp
    exact hpow.symm ▸ idealMultipleι_top_isIso X α F
  exact asIso (idealMultipleι X α F (I ^ 0))

/-- Scalar evaluation for the zero ideal is the zero map. -/
theorem idealEvaluation_bot_eq_zero : idealEvaluation X α F ⊥ = 0 := by
  apply Sigma.hom_ext
  intro a
  have ha : (a : A) = 0 := a.property
  simp [idealEvaluation, globalScalarEndomorphism, ha]

/-- The zero ideal generates the zero subsheaf. -/
theorem idealMultipleι_bot_eq_zero : idealMultipleι X α F ⊥ = 0 := by
  apply (cancel_epi (factorThruImage (idealEvaluation X α F ⊥))).mp
  rw [comp_zero]
  change factorThruImage (idealEvaluation X α F ⊥) ≫
    image.ι (idealEvaluation X α F ⊥) = 0
  rw [image.fac, idealEvaluation_bot_eq_zero]

/-- The original reduction modulo the zero ideal is an isomorphism. -/
theorem idealQuotientπ_bot_isIso : IsIso (idealQuotientπ X α F ⊥) := by
  exact cokernel.π_of_zero (idealMultipleι_bot_eq_zero X α F)

/-- All unit-ideal power quotients vanish, including degree zero. -/
theorem idealPowerQuotient_top_isZero (n : ℕ) :
    IsZero (idealPowerQuotient X α F ⊤ n) := by
  simpa [idealPowerQuotient, ← Ideal.one_eq_top] using idealQuotient_top_isZero X α F

end AlgebraicGeometry.Scheme.Modules
