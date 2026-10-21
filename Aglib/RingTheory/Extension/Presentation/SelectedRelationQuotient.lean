/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.SelectedJacobianChart
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# The actual quotient map from selected relations

Selecting relations from a presentation constructs an intermediate quotient,
not a replacement for the original source. Its canonical surjection onto the
original source remains surjective after inverting its selected Jacobian and
then localizing at an actual prime of the target open.
-/

@[expose] public noncomputable section

universe u v w t z

open MvPolynomial

namespace Algebra.Presentation

variable {R : Type u} {B : Type v} {ι : Type w} {σ : Type t} {τ : Type z}
variable [CommRing R] [CommRing B] [Algebra R B]
variable (P : Presentation R B ι σ) (e : τ → σ)

/-- The literal polynomial quotient by the selected original relations. -/
abbrev SelectedRelationQuotient :=
  MvPolynomial ι R ⧸ Ideal.span (Set.range (P.relation ∘ e))

/-- The intermediate quotient maps to the original algebra through the
original coordinate evaluation, not through new chosen coordinates. -/
def selectedRelationQuotientMap : P.SelectedRelationQuotient e →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ (aeval P.val) (by
    intro p hp
    have hker : Ideal.span (Set.range (P.relation ∘ e)) ≤
        RingHom.ker (aeval P.val).toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact P.aeval_val_relation (e j)
    exact hker hp)

@[simp]
theorem selectedRelationQuotientMap_mk (p : MvPolynomial ι R) :
    P.selectedRelationQuotientMap e (Ideal.Quotient.mk _ p) = aeval P.val p := rfl

/-- No relations beyond the original ones are imposed on the target. -/
theorem selectedRelationQuotientMap_surjective :
    Function.Surjective (P.selectedRelationQuotientMap e) := by
  intro b
  exact ⟨Ideal.Quotient.mk _ (P.σ b), P.aeval_val_σ b⟩

variable (a : τ → ι) (ha : Function.Injective a)

/-- The selected variables and relations give the actual rectangular native
pre-submersive presentation. -/
abbrev selectedRelationPresentation :
    PreSubmersivePresentation R (P.SelectedRelationQuotient e) ι τ :=
  PreSubmersivePresentation.naive (v := P.relation ∘ e) a ha

variable [Finite ι] [Finite τ]

/-- The source of the selected-Jacobian surjection. -/
abbrev SelectedJacobianSource :=
  Localization.Away (P.selectedRelationPresentation e a ha).jacobian

/-- The corresponding actual principal open of the original algebra. -/
abbrev SelectedJacobianTarget :=
  Localization.Away
    (P.selectedRelationQuotientMap e (P.selectedRelationPresentation e a ha).jacobian)

/-- The canonical map after inverting the same actual Jacobian on both sides. -/
def selectedJacobianQuotientMap :
    P.SelectedJacobianSource e a ha →ₐ[R] P.SelectedJacobianTarget e a ha :=
  IsLocalization.Away.mapₐ _ _ (P.selectedRelationQuotientMap e)
    (P.selectedRelationPresentation e a ha).jacobian

omit [Finite ι] in
theorem selectedJacobianQuotientMap_surjective :
    Function.Surjective (P.selectedJacobianQuotientMap e a ha) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective _
    (P.selectedRelationQuotientMap_surjective e)

/-- The actual selected-equation chart has the expected remaining dimension. -/
theorem selectedJacobianSource_isStandardSmoothOfRelativeDimension :
    IsStandardSmoothOfRelativeDimension (Nat.card ι - Nat.card τ) R
      (P.SelectedJacobianSource e a ha) :=
  (P.selectedRelationPresentation e a ha).isStandardSmoothOfRelativeDimension_away_selectedJacobian

variable (q : Ideal (P.SelectedJacobianTarget e a ha)) [q.IsPrime]

/-- The actual map on local rings at the target prime and its inverse image. -/
def selectedJacobianLocalMap :
    Localization.AtPrime (q.comap (P.selectedJacobianQuotientMap e a ha).toRingHom) →ₐ[R]
      Localization.AtPrime q :=
  Localization.localAlgHom _ q (P.selectedJacobianQuotientMap e a ha) rfl

omit [Finite ι] in
/-- This is a surjective map of the actual local rings, before any argument
that its kernel vanishes. -/
theorem selectedJacobianLocalMap_surjective :
    Function.Surjective (P.selectedJacobianLocalMap e a ha q) :=
  (RingHom.surjectiveOnStalks_of_surjective
    (P.selectedJacobianQuotientMap_surjective e a ha)).localRingHom_surjective _ q rfl

end Algebra.Presentation
