/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The original tuple nerve of a family over an object

Families in `Over W` are encoded as a map of presheaves on the original category.
Its tuples are represented by the original finite products in `Over W`.
No preservation of injectives by restriction to a slice is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe w h c

variable {C : Type c} [Category.{h} C] {ι : Type w}

/-- The explicit coproduct of representables for a family. -/
def familyPresheaf (U : ι → C) : Cᵒᵖ ⥤ Type (max w h) where
  obj X := Σ i, X.unop ⟶ U i
  map f := ↾fun x => ⟨x.1, f.unop ≫ x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, g⟩
    change (⟨i, 𝟙 _ ≫ g⟩ : Σ i, X.unop ⟶ U i) = ⟨i, g⟩
    rw [Category.id_comp]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, k⟩
    change (⟨i, (g.unop ≫ f.unop) ≫ k⟩ : Σ i, _ ⟶ U i) =
      ⟨i, g.unop ≫ (f.unop ≫ k)⟩
    rw [Category.assoc]

variable {W : C} (U : ι → Over W)

/-- The map from the family of representables to the represented base object. -/
def familyMap : familyPresheaf (fun i => (U i).left) ⟶ uliftYoneda.{w}.obj W where
  app X := ↾fun x => ⟨x.2 ≫ (U x.1).hom⟩
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro x
    change ULift.up ((f.unop ≫ x.2) ≫ (U x.1).hom) =
      ULift.up (f.unop ≫ (x.2 ≫ (U x.1).hom))
    rw [Category.assoc]

variable [HasFiniteProducts (Over W)]

/-- The canonical map from the source object of a tuple to its product in the slice. -/
def tupleProductLift {n : ℕ} {X : Cᵒᵖ} (t : Tuple (familyMap U) n X) :
    Over.mk t.1.down ⟶ ∏ᶜ (fun i : Fin (n + 1) => U (t.2 i).1.1) :=
  Pi.lift fun i => Over.homMk (t.2 i).1.2
    (congrArg ULift.down (t.2 i).2)

/-- A tuple determines a map to the corresponding fiber product. -/
def tupleToProduct {n : ℕ} {X : Cᵒᵖ} (t : Tuple (familyMap U) n X) :
    (familyPresheaf (fun a : Fin (n + 1) → ι =>
      (∏ᶜ fun i => U (a i)).left)).obj X :=
  ⟨fun i => (t.2 i).1.1, (tupleProductLift U t).left⟩

/-- A map to a fiber product determines its original tuple of lifts. -/
def productToTuple {n : ℕ} {X : Cᵒᵖ}
    (s : (familyPresheaf (fun a : Fin (n + 1) → ι =>
      (∏ᶜ fun i => U (a i)).left)).obj X) : Tuple (familyMap U) n X :=
  ⟨⟨s.2 ≫ (∏ᶜ fun i => U (s.1 i)).hom⟩, fun i =>
    ⟨⟨s.1 i, s.2 ≫ (Pi.π (fun j => U (s.1 j)) i).left⟩, by
      apply ULift.ext
      change (s.2 ≫ (Pi.π (fun j => U (s.1 j)) i).left) ≫ (U (s.1 i)).hom = _
      rw [Category.assoc, Over.w]⟩⟩

lemma productToTuple_tupleToProduct {n : ℕ} {X : Cᵒᵖ}
    (t : Tuple (familyMap U) n X) : productToTuple U (tupleToProduct U t) = t := by
  apply tuple_ext
  · apply ULift.ext
    exact Over.w (tupleProductLift U t)
  · intro i
    change (⟨(t.2 i).1.1, (tupleProductLift U t).left ≫
      (Pi.π (fun j => U (t.2 j).1.1) i).left⟩ : Σ j, X.unop ⟶ (U j).left) = (t.2 i).1
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact congrArg (fun f => f.left) (Pi.lift_comp_π
        (fun j => Over.homMk (U := Over.mk t.1.down) (V := U (t.2 j).1.1)
          (t.2 j).1.2 (congrArg ULift.down (t.2 j).2)) i)

lemma tupleToProduct_productToTuple {n : ℕ} {X : Cᵒᵖ}
    (s : (familyPresheaf (fun a : Fin (n + 1) → ι =>
      (∏ᶜ fun i => U (a i)).left)).obj X) : tupleToProduct U (productToTuple U s) = s := by
  change (⟨s.1, (tupleProductLift U (productToTuple U s)).left⟩ :
    Σ a : Fin (n + 1) → ι, X.unop ⟶ (∏ᶜ fun i => U (a i)).left) = s
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change (tupleProductLift U (productToTuple U s)).left = s.2
  have h : tupleProductLift U (productToTuple U s) = Over.homMk s.2 := by
    apply Pi.hom_ext
    intro i
    simp only [tupleProductLift, Pi.lift_comp_π]
    ext
    rfl
  exact congrArg (fun f => f.left) h

/-- The original tuple terms are represented by the actual slice products. -/
def tupleProductEquiv (n : ℕ) (X : Cᵒᵖ) :
    Tuple (familyMap U) n X ≃
      (familyPresheaf (fun a : Fin (n + 1) → ι =>
        (∏ᶜ fun i => U (a i)).left)).obj X where
  toFun := tupleToProduct U
  invFun := productToTuple U
  left_inv := productToTuple_tupleToProduct U
  right_inv := tupleToProduct_productToTuple U

end CategoryTheory.Presheaf.Cech
