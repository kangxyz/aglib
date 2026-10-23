/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Binary.Compatibility

/-!
# Original binary overlap arrows after pullback

The binary descent arrow is the original given overlap isomorphism pulled
back along the actual test map. On a commuting square of covers, the
native descent pull functor therefore retains the original overlap map,
conjugated only by the native pseudofunctor square comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Opposite CategoryTheory.Limits

namespace CategoryTheory.Pseudofunctor.BinaryDescent

open LocallyDiscreteOpToCat

universe t v v' u u'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- The native contravariant square comparison for an actual commuting square. -/
def squareIso {W' W X' X : C} (b : W' ⟶ W) (p' : W' ⟶ X')
    (p : W ⟶ X) (a : X' ⟶ X) (w : b ≫ p = p' ≫ a) :
    (F.map a.op.toLoc).toFunctor ⋙ (F.map p'.op.toLoc).toFunctor ≅
      (F.map p.op.toLoc).toFunctor ⋙ (F.map b.op.toLoc).toFunctor :=
  Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk w).op.toLoc)

private theorem squareComparison_eq {W' W X' X : C} (b : W' ⟶ W) (p' : W' ⟶ X')
    (p : W ⟶ X) (a : X' ⟶ X) (w : b ≫ p = p' ≫ a) :
    F.isoMapOfCommSq (CommSq.mk w).op.toLoc =
      (F.mapComp a.op.toLoc p'.op.toLoc).symm ≪≫
        F.mapComp' p.op.toLoc b.op.toLoc (p' ≫ a).op.toLoc (by rw [← w]; rfl) := by
  have hc : F.mapComp' a.op.toLoc p'.op.toLoc (p' ≫ a).op.toLoc (by rfl) =
      F.mapComp a.op.toLoc p'.op.toLoc := F.mapComp'_eq_mapComp _ _
  exact (F.isoMapOfCommSq_eq (CommSq.mk w).op.toLoc (p' ≫ a).op.toLoc (by rfl)).trans
    (congrArg (fun z => z.symm ≪≫
      F.mapComp' p.op.toLoc b.op.toLoc (p' ≫ a).op.toLoc (by rw [← w]; rfl)) hc)

/-- The native square comparison expressed through its original composition maps. -/
theorem squareIso_hom {W' W X' X : C} (b : W' ⟶ W) (p' : W' ⟶ X')
    (p : W ⟶ X) (a : X' ⟶ X) (w : b ≫ p = p' ≫ a) (M : F.obj (.mk (op X))) :
    (squareIso F b p' p a w).hom.app M =
      (F.mapComp a.op.toLoc p'.op.toLoc).inv.toNatTrans.app M ≫
        (F.mapComp' p.op.toLoc b.op.toLoc (p' ≫ a).op.toLoc
          (by rw [← w]; rfl)).hom.toNatTrans.app M := by
  exact congrArg (fun z : (F.map a.op.toLoc ≫ F.map p'.op.toLoc) ≅
      (F.map p.op.toLoc ≫ F.map b.op.toLoc) => z.hom.toNatTrans.app M)
    (squareComparison_eq F b p' p a w)

/-- The inverse native square comparison uses the reverse original composition maps. -/
theorem squareIso_inv {W' W X' X : C} (b : W' ⟶ W) (p' : W' ⟶ X')
    (p : W ⟶ X) (a : X' ⟶ X) (w : b ≫ p = p' ≫ a) (M : F.obj (.mk (op X))) :
    (squareIso F b p' p a w).inv.app M =
      (F.mapComp' p.op.toLoc b.op.toLoc (p' ≫ a).op.toLoc
        (by rw [← w]; rfl)).inv.toNatTrans.app M ≫
          (F.mapComp a.op.toLoc p'.op.toLoc).hom.toNatTrans.app M := by
  exact congrArg (fun z : (F.map a.op.toLoc ≫ F.map p'.op.toLoc) ≅
      (F.map p.op.toLoc ≫ F.map b.op.toLoc) => z.inv.toNatTrans.app M)
    (squareComparison_eq F b p' p a w)

variable {S X₀ X₁ W : C} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S)
  [Mono f₀] [Mono f₁] (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁)
  (h : IsPullback p₀ p₁ f₀ f₁)
  (A : F.obj (.mk (op X₀))) (B : F.obj (.mk (op X₁)))
  (e : (F.map p₀.op.toLoc).toFunctor.obj A ≅ (F.map p₁.op.toLoc).toFunctor.obj B)

/-- The original binary overlap arrow on any displayed actual pullback map. -/
theorem hom_eq_pullHom {Y : C} (q : Y ⟶ S) (a : Y ⟶ X₀) (b : Y ⟶ X₁)
    (ha : a ≫ f₀ = q) (hb : b ≫ f₁ = q) (k : Y ⟶ W)
    (hk : k ≫ p₀ = a) (hl : k ≫ p₁ = b) :
    (descentData F f₀ f₁ p₀ p₁ h A B e).hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩)
        q a b ha hb = pullHom e.hom k a b hk hl := by
  change pullHom e.hom (h.lift a b (ha.trans hb.symm)) a b
    (h.lift_fst _ _ _) (h.lift_snd _ _ _) = _
  apply pullHom_congr_left e.hom
  apply h.hom_ext
  · exact (h.lift_fst _ _ _).trans hk.symm
  · exact (h.lift_snd _ _ _).trans hl.symm

/-- On the original overlap itself, the binary descent arrow is exactly
the specified original overlap map. -/
@[simp]
theorem hom_overlap :
    (descentData F f₀ f₁ p₀ p₁ h A B e).hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩)
        (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm = e.hom := by
  rw [hom_eq_pullHom F f₀ f₁ p₀ p₁ h A B e _ _ _ _ _ (𝟙 W)
    (Category.id_comp _) (Category.id_comp _)]
  exact pullHom_id e.hom

variable {S' X₀' X₁' W' : C} (f₀' : X₀' ⟶ S') (f₁' : X₁' ⟶ S')
  (i : S' ⟶ S)
  (g : ∀ j : ULift.{t} Bool,
    family (X₀ := X₀') (X₁ := X₁') j ⟶ family (X₀ := X₀) (X₁ := X₁) j)
  (w : ∀ j, g j ≫ arrows f₀ f₁ j = arrows f₀' f₁' j ≫ i)
  (p₀' : W' ⟶ X₀') (p₁' : W' ⟶ X₁') (h' : p₀' ≫ f₀' = p₁' ≫ f₁')
  (k : W' ⟶ W) (h₀ : k ≫ p₀ = p₀' ≫ g ⟨false⟩)
  (h₁ : k ≫ p₁ = p₁' ≫ g ⟨true⟩)

/-- The single overlap arrow of the original native descent pull functor
is the original pulled overlap map, with the two canonical square comparisons. -/
theorem pullFunctor_hom_overlap :
    ((DescentData.pullFunctor F
      (f := fun j : ULift.{t} Bool => arrows f₀ f₁ j)
      (f' := fun j : ULift.{t} Bool => arrows f₀' f₁' j)
      (p := i) (α := fun j => j) (p' := g) w).obj
        (descentData F f₀ f₁ p₀ p₁ h A B e)).hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩)
        (p₀' ≫ f₀') p₀' p₁' rfl h'.symm =
      (squareIso F k p₀' p₀ (g ⟨false⟩) h₀).hom.app A ≫
        (F.map k.op.toLoc).toFunctor.map e.hom ≫
          (squareIso F k p₁' p₁ (g ⟨true⟩) h₁).inv.app B := by
  have ha : (p₀' ≫ g ⟨false⟩) ≫ f₀ = (p₀' ≫ f₀') ≫ i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z : X₀' ⟶ S => p₀' ≫ z) (w ⟨false⟩)).trans
        (Category.assoc _ _ _).symm)
  have hb : (p₁' ≫ g ⟨true⟩) ≫ f₁ = (p₀' ≫ f₀') ≫ i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z : X₁' ⟶ S => p₁' ≫ z) (w ⟨true⟩)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z : W' ⟶ S' => z ≫ i) h'.symm)))
  change (F.mapComp (g ⟨false⟩).op.toLoc p₀'.op.toLoc).inv.toNatTrans.app A ≫
    (descentData F f₀ f₁ p₀ p₁ h A B e).hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩)
      ((p₀' ≫ f₀') ≫ i) (p₀' ≫ g ⟨false⟩) (p₁' ≫ g ⟨true⟩) ha hb ≫
        (F.mapComp (g ⟨true⟩).op.toLoc p₁'.op.toLoc).hom.toNatTrans.app B = _
  rw [hom_eq_pullHom F f₀ f₁ p₀ p₁ h A B e _ _ _ ha hb k h₀ h₁,
    squareIso_hom, squareIso_inv]
  simp only [pullHom, Category.assoc]

end CategoryTheory.Pseudofunctor.BinaryDescent
