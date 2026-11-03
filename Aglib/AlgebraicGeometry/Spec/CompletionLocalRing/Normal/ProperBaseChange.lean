/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing.Normal

/-! # Proper regular models after completion base change -/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct ChangeOfRings

private theorem localRing_idempotent_eq_zero_or_one
    {A : Type u} [CommRing A] [IsLocalRing A] (a : A) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · right
    apply hu.mul_left_cancel
    simpa only [mul_one] using ha.eq
  · left
    apply hu.mul_left_cancel
    rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]

namespace AlgebraicGeometry.Scheme.LocalRing

section Completion

variable (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
  {Z : Scheme.{u}} (p : Z ⟶ Spec (.of B)) [IsProper p]
  (hZ : RegularStalks Z) (hβ : Function.Bijective (properStructuralSectionsMap p))

include p hZ hβ in
/-- The literal completed pullback of a proper regular model with bijective
original structural sections is integral and normal. Its original section
comparison gives connectedness before any domain property of the completion
is assumed. -/
theorem integral_normal_completionBaseChange_of_proper_regular_structuralSections :
    IsIntegral (pullback p (completionSpecMap B)) ∧
      NormalStalks (pullback p (completionSpecMap B)) := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal B) B
  let W : Scheme.{u} := pullback p (completionSpecMap B)
  let q : W ⟶ Spec (.of S) := pullback.snd p (completionSpecMap B)
  let : IsNoetherianRing S := AdicCompletion.isNoetherianRing B (IsLocalRing.maximalIdeal B)
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian q
  let e : S ≃+* Γ(W, ⊤) := completionStructuralSectionsEquiv B p hβ
  let : Nontrivial Γ(W, ⊤) := e.symm.toEquiv.nontrivial
  let : IsLocalRing Γ(W, ⊤) := e.isLocalRing
  have hWreg : RegularStalks W := (regularStalks_completionBaseChange_iff B p).mp hZ
  have hWnormal : NormalStalks W := by
    intro z
    let : IsRegularLocalRing (W.presheaf.stalk z) := hWreg z
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  let : Nonempty W := by
    by_contra h
    let : IsEmpty W := not_nonempty_iff.mp h
    have ht : (⊤ : W.Opens) = ⊥ := by ext z; exact isEmptyElim z
    have : Subsingleton Γ(W, ⊤) := by rw [ht]; infer_instance
    exact one_ne_zero (Subsingleton.elim (1 : Γ(W, ⊤)) 0)
  let : ConnectedSpace W := connectedSpace_of_globalSections_idempotents W
    (fun a ha => localRing_idempotent_eq_zero_or_one a ha)
  let : IsIntegral W := isIntegral_of_connected_normalStalks_actual W hWnormal
  exact ⟨inferInstance, hWnormal⟩

end Completion

end AlgebraicGeometry.Scheme.LocalRing
