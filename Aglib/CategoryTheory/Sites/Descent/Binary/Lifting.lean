/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Binary.Pullback

/-!
# Lifting binary descent through actual local and overlap isomorphisms

Two specified local lifts and lifting of the one required overlap
isomorphism give an actual lifted descent datum. Its native pullback is
identified with the specified original datum. Effectivity and the local
isomorphism-lifting supplier remain with their respective consumers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Opposite CategoryTheory.Limits

namespace CategoryTheory.Pseudofunctor.BinaryDescent

universe t v v' u u'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S X₀ X₁ W S' X₀' X₁' W' : C}
  (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) [Mono f₀] [Mono f₁]
  (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁) (h : IsPullback p₀ p₁ f₀ f₁)
  (A : F.obj (.mk (op X₀))) (B : F.obj (.mk (op X₁)))
  (f₀' : X₀' ⟶ S') (f₁' : X₁' ⟶ S') [Mono f₀'] [Mono f₁']
  (i : S' ⟶ S)
  (g : ∀ j : ULift.{t} Bool,
    family (X₀ := X₀') (X₁ := X₁') j ⟶ family (X₀ := X₀) (X₁ := X₁) j)
  (w : ∀ j, g j ≫ arrows f₀ f₁ j = arrows f₀' f₁' j ≫ i)
  (p₀' : W' ⟶ X₀') (p₁' : W' ⟶ X₁') (h' : IsPullback p₀' p₁' f₀' f₁')
  (k : W' ⟶ W) (h₀ : k ≫ p₀ = p₀' ≫ g ⟨false⟩)
  (h₁ : k ≫ p₁ = p₁' ≫ g ⟨true⟩)
  (D' : F.DescentData (fun j : ULift.{t} Bool => arrows f₀' f₁' j))
  (a : ∀ j, (F.map (g j).op.toLoc).toFunctor.obj (localObject F A B j) ≅ D'.obj j)

include h' h₀ h₁ a

/-- Local objects with their specified comparisons and lifting of the
required overlap isomorphism produce a genuine lifted native descent
datum, together with its original pullback comparison. -/
theorem exists_overlap_lift_comparison
    (hlift : ∀ e' :
      (F.map k.op.toLoc).toFunctor.obj ((F.map p₀.op.toLoc).toFunctor.obj A) ≅
        (F.map k.op.toLoc).toFunctor.obj ((F.map p₁.op.toLoc).toFunctor.obj B),
      ∃ e : (F.map p₀.op.toLoc).toFunctor.obj A ≅ (F.map p₁.op.toLoc).toFunctor.obj B,
        (F.map k.op.toLoc).toFunctor.map e.hom = e'.hom) :
    ∃ e : (F.map p₀.op.toLoc).toFunctor.obj A ≅ (F.map p₁.op.toLoc).toFunctor.obj B,
      Nonempty (((DescentData.pullFunctor F
        (f := fun j : ULift.{t} Bool => arrows f₀ f₁ j)
        (f' := fun j : ULift.{t} Bool => arrows f₀' f₁' j)
        (p := i) (α := fun j => j) (p' := g) w).obj
          (descentData F f₀ f₁ p₀ p₁ h A B e)) ≅ D') := by
  let t₀ := (squareIso F k p₀' p₀ (g ⟨false⟩) h₀).app A
  let t₁ := (squareIso F k p₁' p₁ (g ⟨true⟩) h₁).app B
  let a₀ := (F.map p₀'.op.toLoc).toFunctor.mapIso (a ⟨false⟩)
  let a₁ := (F.map p₁'.op.toLoc).toFunctor.mapIso (a ⟨true⟩)
  let z := D'.iso (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀' ≫ f₀') p₀' p₁' rfl h'.w.symm
  let e' := t₀.symm ≪≫ a₀ ≪≫ z ≪≫ a₁.symm ≪≫ t₁
  obtain ⟨e, he⟩ := hlift e'
  refine ⟨e, ⟨?_⟩⟩
  apply isoMk F f₀' f₁' p₀' p₁' h' _ D' a
  rw [pullFunctor_hom_overlap F f₀ f₁ p₀ p₁ h A B e f₀' f₁' i g w
    p₀' p₁' h'.w k h₀ h₁, he]
  change a₀.hom ≫ z.hom = (t₀.hom ≫ e'.hom ≫ t₁.inv) ≫ a₁.hom
  simp only [e', Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.Pseudofunctor.BinaryDescent
