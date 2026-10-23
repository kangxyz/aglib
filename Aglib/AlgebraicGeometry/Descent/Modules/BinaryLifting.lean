/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.BinaryGluing
public import Aglib.CategoryTheory.Sites.Descent.Binary.Lifting

/-!
# Global line-bundle lifting from two local lifts

Actual local lifts and lifting of the one required overlap isomorphism
give a global line bundle. The native pull functor on descent data and the
original open-cover full faithfulness identify its original pullback with
the specified target bundle. This is the assembly theorem; the affine
square-zero consumer proves the local lifting hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pseudofunctor.BinaryDescent

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {S X₀ X₁ W S' X₀' X₁' W' : Scheme.{u}}

/-- Two actual local lifts with their specified comparisons and actual
overlap-isomorphism lifting give a global lift with an actual original
pullback isomorphism. -/
theorem exists_lineBundle_lift_of_binary
    (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁) (h : IsPullback p₀ p₁ f₀ f₁)
    (hcover : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (A : LineBundle X₀) (B : LineBundle X₁)
    (f₀' : X₀' ⟶ S') (f₁' : X₁' ⟶ S') [IsOpenImmersion f₀'] [IsOpenImmersion f₁']
    (hcover' : f₀'.opensRange ⊔ f₁'.opensRange = ⊤) (i : S' ⟶ S)
    (g : ∀ j : ULift.{u} Bool,
      family (X₀ := X₀') (X₁ := X₁') j ⟶ family (X₀ := X₀) (X₁ := X₁) j)
    (w : ∀ j, g j ≫ arrows f₀ f₁ j = arrows f₀' f₁' j ≫ i)
    (p₀' : W' ⟶ X₀') (p₁' : W' ⟶ X₁') (h' : IsPullback p₀' p₁' f₀' f₁')
    (k : W' ⟶ W) (h₀ : k ≫ p₀ = p₀' ≫ g ⟨false⟩)
    (h₁ : k ≫ p₁ = p₁' ≫ g ⟨true⟩) (L : LineBundle S')
    (a : ∀ j, (pullback (g j)).obj (localObject pullbackPseudofunctor A.val B.val j) ≅
      (pullback (arrows f₀' f₁' j)).obj L.val)
    (hlift : ∀ e' : (pullback k).obj ((pullback p₀).obj A.val) ≅
      (pullback k).obj ((pullback p₁).obj B.val),
      ∃ e : (pullback p₀).obj A.val ≅ (pullback p₁).obj B.val,
        (pullback k).map e.hom = e'.hom) :
    ∃ M : LineBundle S, Nonempty ((pullback i).obj M.val ≅ L.val) := by
  let D' := (pullbackPseudofunctor.toDescentData
    (fun j : ULift.{u} Bool => arrows f₀' f₁' j)).obj L.val
  obtain ⟨e, ⟨he⟩⟩ := exists_overlap_lift_comparison pullbackPseudofunctor f₀ f₁
    p₀ p₁ h A.val B.val f₀' f₁' i g w p₀' p₁' h' k h₀ h₁ D' a hlift
  let M := BinaryGluing.lineBundle f₀ f₁ p₀ p₁ h A B e hcover
  let P := Pseudofunctor.DescentData.pullFunctor pullbackPseudofunctor
    (f := fun j : ULift.{u} Bool => arrows f₀ f₁ j)
    (f' := fun j : ULift.{u} Bool => arrows f₀' f₁' j)
    (p := i) (α := fun j => j) (p' := g) w
  let t := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso pullbackPseudofunctor
    (f := fun j : ULift.{u} Bool => arrows f₀ f₁ j)
    (f' := fun j : ULift.{u} Bool => arrows f₀' f₁' j)
    (p := i) (α := fun j => j) (p' := g) w
  let eD := (t.app M.val).symm ≪≫
    P.mapIso (BinaryGluing.comparisonIso f₀ f₁ p₀ p₁ h A B e hcover) ≪≫ he
  have hfamily := BinaryGluing.family_covers f₀' f₁' hcover'
  have hpoints : ∀ x : S', ∃ (j : ULift.{u} Bool)
      (y : family (C := Scheme.{u}) (X₀ := X₀') (X₁ := X₁') j),
      arrows f₀' f₁' j y = x := by
    intro x
    have hx : x ∈ iSup (fun j : ULift.{u} Bool => (arrows f₀' f₁' j).opensRange) := by
      rw [hfamily]
      trivial
    obtain ⟨j, y, hy⟩ := Opens.mem_iSup.mp hx
    exact ⟨j, y, hy⟩
  exact ⟨M, ⟨(fullyFaithfulToDescentDataOfOpenImmersion
    (fun j : ULift.{u} Bool => arrows f₀' f₁' j) hpoints).preimageIso eD⟩⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
