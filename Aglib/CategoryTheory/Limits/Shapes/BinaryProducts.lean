/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero morphisms into binary products

A binary-product-preserving functor detects a zero mapped morphism into a product from its two
mapped projections. The source and target categories are independent.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/GluingSubobjects.lean`.
SHA-256: `d6329afc8058687c07b626f0cf1a82a708d6ed99bcdda9d8fc260402bd0c28a9`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits

/-- A morphism into a binary product is zero if both components vanish,
and the same holds after applying a product-preserving functor. -/
lemma map_prod_lift_comp_eq_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D)
    {T Y Z : C} [HasBinaryProduct Y Z] [PreservesLimit (pair Y Z) F]
    {A : D} (i : A ⟶ F.obj T) (f : T ⟶ Y) (g : T ⟶ Z)
    (hf : i ≫ F.map f = 0) (hg : i ≫ F.map g = 0) :
    i ≫ F.map (prod.lift f g) = 0 := by
  apply (isLimitOfPreserves F (prodIsProd Y Z)).hom_ext
  rintro (_ | _)
  · change (i ≫ F.map (prod.lift f g)) ≫ F.map prod.fst = 0 ≫ F.map prod.fst
    simp only [Category.assoc, ← F.map_comp, prod.lift_fst, hf, zero_comp]
  · change (i ≫ F.map (prod.lift f g)) ≫ F.map prod.snd = 0 ≫ F.map prod.snd
    simp only [Category.assoc, ← F.map_comp, prod.lift_snd, hg, zero_comp]

end CategoryTheory.Limits
