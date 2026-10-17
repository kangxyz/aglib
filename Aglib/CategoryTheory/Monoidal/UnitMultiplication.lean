/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Multiplication by a morphism out of the tensor unit

In a monoidal category, a morphism `σ : 𝟙_ C ⟶ A` multiplies every object:
`unitMultiply σ F = (λ_ F).inv ≫ σ ▷ F : F ⟶ A ⊗ F`. It is natural in `F`
(`unitMultiply_naturality`) and, on a tensor product, it is multiplication on the first factor
followed by the associator (`unitMultiply_whiskerRight_associator`). In a braided category it
commutes with a left tensor factor up to the braiding (`whiskerLeft_unitMultiply`).

For a lax monoidal functor `F : C ⥤ D` and `σ : 𝟙_ D ⟶ F.obj X`, the composite
`unitMultiply σ (F.obj Y) ≫ μ F X Y : F.obj Y ⟶ F.obj (X ⊗ Y)` is compatible with the
tensorator on an outer factor (`Functor.LaxMonoidal.unitMultiply_μ_whiskerRight`) and, for a
lax braided functor, on an inner factor (`Functor.LaxBraided.whiskerLeft_unitMultiply_μ`). Both
proofs use only associator and unitor naturality, `whisker_exchange`, the associativity of `μ`
and, for the inner factor, the braiding compatibility of `μ`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory BraidedCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

namespace MonoidalCategory

/-- Multiplication by a morphism out of the tensor unit: `F ≅ 𝟙_ C ⊗ F ⟶ A ⊗ F`. -/
def unitMultiply {A : C} (σ : 𝟙_ C ⟶ A) (F : C) : F ⟶ A ⊗ F :=
  (λ_ F).inv ≫ σ ▷ F

theorem unitMultiply_def {A : C} (σ : 𝟙_ C ⟶ A) (F : C) :
    unitMultiply σ F = (λ_ F).inv ≫ σ ▷ F :=
  rfl

/-- Multiplication by `σ` is natural in the multiplied object. -/
@[reassoc]
theorem unitMultiply_naturality {A : C} (σ : 𝟙_ C ⟶ A) {F G : C} (f : F ⟶ G) :
    f ≫ unitMultiply σ G = unitMultiply σ F ≫ A ◁ f := by
  rw [unitMultiply, unitMultiply, leftUnitor_inv_naturality_assoc, assoc, whisker_exchange]

/-- Multiplication on a tensor product is multiplication on its first factor, followed by the
associator. -/
@[reassoc]
theorem unitMultiply_whiskerRight_associator {A : C} (σ : 𝟙_ C ⟶ A) (F G : C) :
    unitMultiply σ F ▷ G ≫ (α_ A F G).hom = unitMultiply σ (F ⊗ G) := by
  rw [unitMultiply, unitMultiply, comp_whiskerRight, assoc, associator_naturality_left,
    leftUnitor_inv_whiskerRight_assoc, Iso.inv_hom_id_assoc]

/-- In a braided category, multiplication commutes with a left tensor factor up to the
braiding. -/
theorem whiskerLeft_unitMultiply [BraidedCategory C] {A : C} (σ : 𝟙_ C ⟶ A) (B F : C) :
    B ◁ unitMultiply σ F =
      unitMultiply σ (B ⊗ F) ≫ (α_ A B F).inv ≫ (β_ A B).hom ▷ F ≫ (α_ B A F).hom := by
  rw [unitMultiply, unitMultiply, assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle, ← leftUnitor_inv_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, leftUnitor_inv_braiding, triangle_assoc_comp_right_inv_assoc,
    whiskerLeft_comp]

end MonoidalCategory

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Multiplication by `σ : 𝟙_ D ⟶ F.obj X` on an outer tensor factor, followed by the
tensorator, is the tensorator followed by multiplication on the merged factor. -/
theorem Functor.LaxMonoidal.unitMultiply_μ_whiskerRight (F : C ⥤ D) [F.LaxMonoidal] {X : C}
    (σ : 𝟙_ D ⟶ F.obj X) (Y Z : C) :
    (unitMultiply σ (F.obj Y) ≫ μ F X Y) ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
      μ F Y Z ≫ unitMultiply σ (F.obj (Y ⊗ Z)) ≫ μ F X (Y ⊗ Z) := by
  rw [comp_whiskerRight, assoc, associativity, unitMultiply_whiskerRight_associator_assoc,
    ← unitMultiply_naturality_assoc]

/-- Multiplication by `σ : 𝟙_ D ⟶ F.obj X` on an inner tensor factor, followed by the
tensorator, is the tensorator followed by multiplication on the merged factor and the image of
the braiding of `X` past `Z`. -/
theorem Functor.LaxBraided.whiskerLeft_unitMultiply_μ [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] {X : C} (σ : 𝟙_ D ⟶ F.obj X) (Y Z : C) :
    F.obj Z ◁ (unitMultiply σ (F.obj Y) ≫ μ F X Y) ≫ μ F Z (X ⊗ Y) =
      μ F Z Y ≫ unitMultiply σ (F.obj (Z ⊗ Y)) ≫ μ F X (Z ⊗ Y) ≫
        F.map ((α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom) := by
  rw [MonoidalCategory.whiskerLeft_comp, assoc, whiskerLeft_unitMultiply, assoc, assoc, assoc,
    ← associativity F Z X Y, ← comp_whiskerRight_assoc, ← Functor.LaxBraided.braided,
    comp_whiskerRight_assoc, μ_natural_left_assoc, ← associativity_inv_assoc,
    ← unitMultiply_naturality_assoc, Functor.map_comp, Functor.map_comp]

end CategoryTheory
