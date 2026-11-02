/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Recovering an actual binary operation from full tests

The operation is evaluated on the projections of its original product test.
Fullness and naturality prove its value on every test. The comparison identifies
that actual product with a supplied test object; no operation equality or
representation of the resulting morphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.RepresentableBinaryOperation

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D] (F : C ⥤ D) {X Y Z : D}
  (η : ∀ U : C, (F.obj U ⟶ X) → (F.obj U ⟶ Y) → (F.obj U ⟶ Z))
  (U₀ : C) (κ : F.obj U₀ ≅ X ⊗ Y)

/-- The actual map is evaluation on the original product-test projections. -/
def map : X ⊗ Y ⟶ Z :=
  κ.inv ≫ η U₀ (κ.hom ≫ fst X Y) (κ.hom ≫ snd X Y)

/-- Actual test naturality proves the entire component value of this map. -/
theorem map_value [F.Full]
    (hη : ∀ {U V : C} (f : U ⟶ V) (a : F.obj V ⟶ X) (b : F.obj V ⟶ Y),
      F.map f ≫ η V a b = η U (F.map f ≫ a) (F.map f ≫ b))
    (U : C) (a : F.obj U ⟶ X) (b : F.obj U ⟶ Y) :
    lift a b ≫ map F η U₀ κ = η U a b := by
  let f : U ⟶ U₀ := F.preimage (lift a b ≫ κ.inv)
  have hf : F.map f = lift a b ≫ κ.inv := F.map_preimage _
  calc
    _ = F.map f ≫ η U₀ (κ.hom ≫ fst X Y) (κ.hom ≫ snd X Y) := by
      rw [hf]
      exact (Category.assoc _ _ _).symm
    _ = η U (F.map f ≫ (κ.hom ≫ fst X Y))
        (F.map f ≫ (κ.hom ≫ snd X Y)) := hη f _ _
    _ = η U a b := by
      rw [hf]
      simp only [Category.assoc, κ.inv_hom_id_assoc, lift_fst, lift_snd]

end CategoryTheory.RepresentableBinaryOperation
