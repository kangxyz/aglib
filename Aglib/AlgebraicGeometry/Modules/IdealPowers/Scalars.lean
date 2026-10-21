/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Basic

/-! # Scalars on actual ideal quotients -/

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

/-- Every scalar in the defining ideal acts by zero on the genuine sheaf quotient. -/
theorem idealQuotient_scalar_eq_zero (J : Ideal A) (a : J) :
    globalScalarEndomorphism X (idealQuotient X α F J) (α a) = 0 := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  rw [(globalScalarCenter X (α a)).naturality]
  change globalScalarEndomorphism X F (α a) ≫ idealQuotientπ X α F J =
    idealQuotientπ X α F J ≫ 0
  rw [← idealMultipleScalar_ι X α F J a, Category.assoc,
    idealMultipleι_quotientπ, comp_zero, comp_zero]

/-- The unit-ideal quotient is zero, without any assumption on the scheme or coefficient. -/
theorem idealQuotient_top_isZero : IsZero (idealQuotient X α F ⊤) := by
  rw [IsZero.iff_id_eq_zero]
  have h := idealQuotient_scalar_eq_zero X α F ⊤ ⟨1, trivial⟩
  simpa [globalScalarEndomorphism, map_one] using h

/-- The zeroth coefficient quotient is zero, retaining the unshifted natural indexing. -/
theorem idealPowerQuotient_zero_isZero (I : Ideal A) :
    IsZero (idealPowerQuotient X α F I 0) := by
  simpa only [idealPowerQuotient, pow_zero, Ideal.one_eq_top] using
    idealQuotient_top_isZero X α F

end AlgebraicGeometry.Scheme.Modules
