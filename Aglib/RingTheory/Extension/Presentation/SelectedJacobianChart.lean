/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Rectangular selected-Jacobian charts with retained relative dimension

Inverting the selected Jacobian of a pre-submersive presentation gives an
actual standard-smooth algebra. The relative dimension remains the number of
variables minus the number of relations. The resulting etale polynomial chart
has exactly that many variables; no unspecified relative rank is introduced.
-/

@[expose] public noncomputable section

universe u v w t

namespace Algebra.PreSubmersivePresentation

variable {R : Type u} {B : Type v} {ι : Type w} {σ : Type t}
variable [CommRing R] [CommRing B] [Algebra R B] [Finite ι] [Finite σ]

/-- Adjoining the inverse of the selected Jacobian adds one equation and one
variable to the actual original presentation. -/
def submersivePresentationAwaySelectedJacobian
    (P : PreSubmersivePresentation R B ι σ) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := (localizationAway (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, localizationAway_jacobian,
      Algebra.smul_def]
    have h : IsUnit (algebraMap B (Localization.Away P.jacobian) P.jacobian) :=
      IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
    exact h.mul h

/-- The actual Jacobian localization has precisely the original presentation
relative dimension, including the empty-equation case. -/
theorem isStandardSmoothOfRelativeDimension_away_selectedJacobian
    (P : PreSubmersivePresentation R B ι σ) :
    IsStandardSmoothOfRelativeDimension P.dimension R (Localization.Away P.jacobian) := by
  apply P.submersivePresentationAwaySelectedJacobian.isStandardSmoothOfRelativeDimension
  change ((localizationAway (Localization.Away P.jacobian) P.jacobian).comp P).dimension = _
  rw [dimension_comp_eq_dimension_add_dimension]
  simp [Presentation.dimension]

/-- The polynomial chart has exactly the retained number of free variables.
This theorem does not claim its variables equal a previously chosen complement. -/
theorem exists_etale_mvPolynomial_away_selectedJacobian
    (P : PreSubmersivePresentation R B ι σ) :
    ∃ g : MvPolynomial (Fin P.dimension) R →ₐ[R] Localization.Away P.jacobian,
      g.Etale := by
  let := P.isStandardSmoothOfRelativeDimension_away_selectedJacobian
  exact IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial P.dimension R _

end Algebra.PreSubmersivePresentation
