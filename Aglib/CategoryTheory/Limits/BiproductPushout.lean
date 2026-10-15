/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Biproducts of displayed pushout squares

Source:
`Quillen/CategoryTheory/Limits/BiproductPushout.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`ffe7ed6ea79b2f1ecfc9fd4d2f2e40a051b2e43710b9d9ffc78b70669a25c0aa`.
Selected declarations: isPushout_biprod_map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {A B D P A' B' D' P' : C}
  {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ P'} {j' : D' ⟶ P'}

/-- The literal biproduct maps of two genuine pushout squares form a pushout.
No admissibility, mono or splitting condition is required. -/
theorem IsPushout.biprod_map (h : IsPushout f g i j) (h' : IsPushout f' g' i' j') :
    IsPushout (biprod.map f f') (biprod.map g g') (biprod.map i i') (biprod.map j j') := by
  have w : biprod.map f f' ≫ biprod.map i i' = biprod.map g g' ≫ biprod.map j j' := by
    ext <;> simp [h.w, h'.w]
  apply IsPushout.mk' w
  · intro X a b hi hj
    apply biprod.hom_ext'
    · apply h.hom_ext
      · simpa using congrArg (fun t ↦ (biprod.inl : B ⟶ B ⊞ B') ≫ t) hi
      · simpa using congrArg (fun t ↦ (biprod.inl : D ⟶ D ⊞ D') ≫ t) hj
    · apply h'.hom_ext
      · simpa using congrArg (fun t ↦ (biprod.inr : B' ⟶ B ⊞ B') ≫ t) hi
      · simpa using congrArg (fun t ↦ (biprod.inr : D' ⟶ D ⊞ D') ≫ t) hj
  · intro X a b hab
    have hab₁ : f ≫ biprod.inl ≫ a = g ≫ biprod.inl ≫ b := by
      simpa using congrArg (fun t ↦ (biprod.inl : A ⟶ A ⊞ A') ≫ t) hab
    have hab₂ : f' ≫ biprod.inr ≫ a = g' ≫ biprod.inr ≫ b := by
      simpa using congrArg (fun t ↦ (biprod.inr : A' ⟶ A ⊞ A') ≫ t) hab
    refine ⟨biprod.desc (h.desc (biprod.inl ≫ a) (biprod.inl ≫ b) hab₁)
      (h'.desc (biprod.inr ≫ a) (biprod.inr ≫ b) hab₂), ?_, ?_⟩
    · apply biprod.hom_ext' <;> simp
    · apply biprod.hom_ext' <;> simp

end CategoryTheory.Limits
