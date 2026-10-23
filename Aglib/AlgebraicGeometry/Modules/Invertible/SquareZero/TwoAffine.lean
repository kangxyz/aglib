/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.BinaryLifting
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.ClosedImmersion

/-!
# Line-bundle lifting on a two-affine cover across a square-zero thickening

Lift on each actual affine chart and lift the specified overlap
isomorphism on the actual affine intersection. Binary descent supplies
the global object and identifies its original pullback with the specified
line bundle. The rings and schemes need not be Noetherian or reduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pseudofunctor.BinaryDescent

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Every line bundle lifts across an intrinsic square-zero closed immersion
when the target has the specified two-affine cover with affine intersection.
The conclusion uses the original scheme pullback and an actual isomorphism. -/
theorem exists_lineBundle_lift_twoAffine_of_square_zero
    {S₀ S X₀ X₁ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : i.ker ^ 2 = ⊥) [IsAffine X₀] [IsAffine X₁]
    (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    [IsAffine (Limits.pullback f₀ f₁)] (hcover : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (L : LineBundle S₀) :
    ∃ M : LineBundle S, Nonempty ((pullback i).obj M.val ≅ L.val) := by
  let Y₀ := Limits.pullback f₀ i
  let Y₁ := Limits.pullback f₁ i
  let g₀ : Y₀ ⟶ X₀ := Limits.pullback.fst f₀ i
  let g₁ : Y₁ ⟶ X₁ := Limits.pullback.fst f₁ i
  let a₀ : Y₀ ⟶ S₀ := Limits.pullback.snd f₀ i
  let a₁ : Y₁ ⟶ S₀ := Limits.pullback.snd f₁ i
  let W := Limits.pullback f₀ f₁
  let p₀ : W ⟶ X₀ := Limits.pullback.fst f₀ f₁
  let p₁ : W ⟶ X₁ := Limits.pullback.snd f₀ f₁
  let V := Limits.pullback p₁ g₁
  let k : V ⟶ W := Limits.pullback.fst p₁ g₁
  let r₁ : V ⟶ Y₁ := Limits.pullback.snd p₁ g₁
  have hg₀ : g₀ ≫ f₀ = a₀ ≫ i := Limits.pullback.condition
  have hg₁ : g₁ ≫ f₁ = a₁ ≫ i := Limits.pullback.condition
  have hp : p₀ ≫ f₀ = p₁ ≫ f₁ := Limits.pullback.condition
  have hk : k ≫ p₁ = r₁ ≫ g₁ := Limits.pullback.condition
  have hcomm : (k ≫ p₀) ≫ f₀ = (r₁ ≫ a₁) ≫ i := by
    calc
      (k ≫ p₀) ≫ f₀ = k ≫ (p₀ ≫ f₀) := Category.assoc _ _ _
      _ = k ≫ (p₁ ≫ f₁) := congrArg (fun z => k ≫ z) hp
      _ = (k ≫ p₁) ≫ f₁ := (Category.assoc _ _ _).symm
      _ = (r₁ ≫ g₁) ≫ f₁ := congrArg (fun z => z ≫ f₁) hk
      _ = r₁ ≫ (g₁ ≫ f₁) := Category.assoc _ _ _
      _ = r₁ ≫ (a₁ ≫ i) := congrArg (fun z => r₁ ≫ z) hg₁
      _ = (r₁ ≫ a₁) ≫ i := (Category.assoc _ _ _).symm
  let r₀ : V ⟶ Y₀ := Limits.pullback.lift (k ≫ p₀) (r₁ ≫ a₁) hcomm
  have hr₀ : r₀ ≫ g₀ = k ≫ p₀ := Limits.pullback.lift_fst _ _ _
  have hr₀' : r₀ ≫ a₀ = r₁ ≫ a₁ := Limits.pullback.lift_snd _ _ _
  have H : IsPullback p₀ p₁ f₀ f₁ := IsPullback.of_hasPullback f₀ f₁
  have H₀ : IsPullback g₀ a₀ f₀ i := IsPullback.of_hasPullback f₀ i
  have H₁ : IsPullback g₁ a₁ f₁ i := IsPullback.of_hasPullback f₁ i
  have HK : IsPullback k r₁ p₁ g₁ := IsPullback.of_hasPullback p₁ g₁
  have H' : IsPullback r₀ r₁ a₀ a₁ :=
    H.paste_twist_right H₀ g₁ a₁ hg₁ k r₁ HK hr₀ hr₀'
  have : IsClosedImmersion g₀ := by dsimp [g₀]; infer_instance
  have : IsClosedImmersion g₁ := by dsimp [g₁]; infer_instance
  have : IsOpenImmersion a₀ := by dsimp [a₀]; infer_instance
  have : IsOpenImmersion a₁ := by dsimp [a₁]; infer_instance
  have : IsOpenImmersion p₁ := by dsimp [p₁]; infer_instance
  have : IsClosedImmersion k := by dsimp [k]; infer_instance
  have : IsAffine Y₀ := by dsimp [Y₀]; infer_instance
  have : IsAffine Y₁ := by dsimp [Y₁]; infer_instance
  have : IsAffine W := inferInstanceAs (IsAffine (Limits.pullback f₀ f₁))
  have : IsAffine V := by dsimp [V]; infer_instance
  have hi₀ : g₀.ker ^ 2 = ⊥ := kernel_sq_of_open_pullback i g₀ a₀ f₀ H₀ hi
  have hi₁ : g₁.ker ^ 2 = ⊥ := kernel_sq_of_open_pullback i g₁ a₁ f₁ H₁ hi
  have hiK : k.ker ^ 2 = ⊥ := kernel_sq_of_open_pullback g₁ k r₁ p₁ HK hi₁
  obtain ⟨A, ⟨eA⟩⟩ := exists_lineBundle_lift_affine_closed_of_square_zero g₀ hi₀
    (pullbackLineBundle a₀ L)
  obtain ⟨B, ⟨eB⟩⟩ := exists_lineBundle_lift_affine_closed_of_square_zero g₁ hi₁
    (pullbackLineBundle a₁ L)
  let g (j : ULift.{u} Bool) : family (X₀ := Y₀) (X₁ := Y₁) j ⟶
      family (X₀ := X₀) (X₁ := X₁) j := by
    rcases j with ⟨j⟩
    cases j
    · exact g₀
    · exact g₁
  have w : ∀ j : ULift.{u} Bool, g j ≫ arrows f₀ f₁ j = arrows a₀ a₁ j ≫ i := by
    rintro ⟨j⟩
    cases j
    · exact hg₀
    · exact hg₁
  have a : ∀ j : ULift.{u} Bool,
      (pullback (g j)).obj (localObject pullbackPseudofunctor A.val B.val j) ≅
        (pullback (arrows a₀ a₁ j)).obj L.val := by
    rintro ⟨j⟩
    cases j
    · exact eA
    · exact eB
  have hcover' : a₀.opensRange ⊔ a₁.opensRange = ⊤ := by
    change (Limits.pullback.snd f₀ i).opensRange ⊔
      (Limits.pullback.snd f₁ i).opensRange = ⊤
    rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.opensRange_pullbackSnd]
    ext x
    change (i x ∈ f₀.opensRange ∨ i x ∈ f₁.opensRange) ↔ True
    change i x ∈ f₀.opensRange ⊔ f₁.opensRange ↔ True
    simp [hcover]
  apply exists_lineBundle_lift_of_binary f₀ f₁ p₀ p₁ H hcover A B a₀ a₁ hcover'
    i g w r₀ r₁ H' k hr₀.symm hk L a
  intro e'
  exact exists_lineBundle_iso_lift_affine_closed_of_square_zero k hiK
    (pullbackLineBundle p₀ A) (pullbackLineBundle p₁ B) e'

end AlgebraicGeometry.Scheme.Modules.Invertible
