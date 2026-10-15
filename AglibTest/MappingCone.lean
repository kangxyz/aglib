/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.MappingCone.Map

/-! Mapping-cone map additivity through the public module interface for an arbitrary
preadditive category with binary biproducts. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

example {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) (a a' : K₁ ⟶ K₂) (b b' : L₁ ⟶ L₂)
    (h : f ≫ b = a ≫ g) (h' : f ≫ b' = a' ≫ g) :
    CochainComplex.mappingCone.map f g (a + a') (b + b')
        (by simp [Preadditive.comp_add, Preadditive.add_comp, h, h']) =
      CochainComplex.mappingCone.map f g a b h + CochainComplex.mappingCone.map f g a' b' h' :=
  CochainComplex.mappingCone.map_add f g a a' b b' h h'
