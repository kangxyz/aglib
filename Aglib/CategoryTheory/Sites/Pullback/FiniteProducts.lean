/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Data.Fintype.Pi

/-! # Original product trivializations and finite actual product values

The comparison is constructed from the original product-preservation maps
and the supplied original trivialization. No replacement product is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe c₁ h₁ c₂ h₂ c₃ h₃ i

variable {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
  {V : Type c₃} [Category.{h₃} V]

/-- The original product map and its inverse use only these two actual products. -/
def selectedProductMapIso {I : Type i} {F G : I → D}
    [HasProduct F] [HasProduct G] (e : ∀ i, F i ≅ G i) : (∏ᶜ F) ≅ ∏ᶜ G where
  hom := CategoryTheory.Limits.Pi.map (fun i => (e i).hom)
  inv := CategoryTheory.Limits.Pi.map (fun i => (e i).inv)
  hom_inv_id := by
    rw [CategoryTheory.Limits.Pi.map_comp_map]
    simp only [Iso.hom_inv_id, CategoryTheory.Limits.Pi.map_id]
  inv_hom_id := by
    rw [CategoryTheory.Limits.Pi.map_comp_map]
    simp only [Iso.inv_hom_id, CategoryTheory.Limits.Pi.map_id]

/-- With the native all-products dictionary, this is the same original Pi.mapIso. -/
theorem selectedProductMapIso_eq_mapIso {I : Type i} {F G : I → D}
    [HasProductsOfShape I D] (e : ∀ i, F i ≅ G i) :
    selectedProductMapIso e = Pi.mapIso e := by
  apply Iso.ext
  rfl

/-- Preserve the original three factors of the product trivialization. -/
def powerTrivializationIso (L : C ⥤ D) (K : V ⥤ D) {F : C} {A : V}
    (e : L.obj F ≅ K.obj A) (I : Type i)
    [HasProduct (fun _ : I => F)] [HasProduct (fun _ : I => A)]
    [HasProduct (fun _ : I => L.obj F)] [HasProduct (fun _ : I => K.obj A)]
    [PreservesLimit (Discrete.functor (fun _ : I => F)) L]
    [PreservesLimit (Discrete.functor (fun _ : I => A)) K] :
    L.obj (∏ᶜ fun _ : I => F) ≅ K.obj (∏ᶜ fun _ : I => A) :=
  PreservesProduct.iso L (fun _ : I => F) ≪≫
    selectedProductMapIso (fun _ : I => e) ≪≫
      (PreservesProduct.iso K (fun _ : I => A)).symm

/-- The original operational product comparison, rather than an arbitrary
isomorphism with these endpoints. -/
theorem powerTrivializationIso_eq_original (L : C ⥤ D) (K : V ⥤ D) {F : C} {A : V}
    (e : L.obj F ≅ K.obj A) (I : Type i)
    [HasProduct (fun _ : I => F)] [HasProduct (fun _ : I => A)]
    [HasProductsOfShape I D]
    [PreservesLimit (Discrete.functor (fun _ : I => F)) L]
    [PreservesLimit (Discrete.functor (fun _ : I => A)) K] :
    powerTrivializationIso L K e I =
      PreservesProduct.iso L (fun _ : I => F) ≪≫
        Pi.mapIso (fun _ : I => e) ≪≫
          (PreservesProduct.iso K (fun _ : I => A)).symm := by
  unfold powerTrivializationIso
  rw [selectedProductMapIso_eq_mapIso]

/-- Even without other products, the forward map is literally the original
projection-induced Pi.map between these selected endpoint products. -/
theorem powerTrivializationIso_hom_eq_original (L : C ⥤ D) (K : V ⥤ D) {F : C} {A : V}
    (e : L.obj F ≅ K.obj A) (I : Type i)
    [HasProduct (fun _ : I => F)] [HasProduct (fun _ : I => A)]
    [HasProduct (fun _ : I => L.obj F)] [HasProduct (fun _ : I => K.obj A)]
    [PreservesLimit (Discrete.functor (fun _ : I => F)) L]
    [PreservesLimit (Discrete.functor (fun _ : I => A)) K] :
    (powerTrivializationIso L K e I).hom =
      (PreservesProduct.iso L (fun _ : I => F)).hom ≫
        CategoryTheory.Limits.Pi.map (fun _ : I => e.hom) ≫
          (PreservesProduct.iso K (fun _ : I => A)).inv := rfl

end CategoryTheory.Functor

namespace AddCommGrpCat

universe i v

/-- The actual categorical finite product is finite by its original
projection map into the dependent tuple, with no change of carrier. -/
theorem finite_power_value (I : Type i) [Finite I] (A : AddCommGrpCat.{v}) [Finite A]
    [HasProduct (fun _ : I => A)] :
    Finite (∏ᶜ (fun _ : I => A) : AddCommGrpCat.{v}) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite A
  apply Finite.of_injective
    (fun x : (∏ᶜ (fun _ : I => A) : AddCommGrpCat.{v}) =>
      fun i : I => (Pi.π (fun _ : I => A) i) x)
  intro x y h
  exact Concrete.limit_ext (Discrete.functor (fun _ : I => A)) x y
    (fun i => congrFun h i.as)

end AddCommGrpCat
