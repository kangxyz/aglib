/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Additivity of actual mapping-cone maps

Source:
`Quillen/Algebra/Homology/MappingConeBiprod.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`4b95511976c458eb12ca317b8f4ac2190ccdcdd40f065cdc57c796359d8b291c`.
Selected declarations: mappingCone_map_add.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The map of actual mapping cones is additive in the two maps of the commutative square. -/
lemma mappingCone.map_add {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) (a a' : K₁ ⟶ K₂) (b b' : L₁ ⟶ L₂)
    (h : f ≫ b = a ≫ g) (h' : f ≫ b' = a' ≫ g) :
    mappingCone.map f g (a + a') (b + b') (by simp [Preadditive.comp_add, Preadditive.add_comp, h,
      h']) =
      mappingCone.map f g a b h + mappingCone.map f g a' b' h' := by
  ext n
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map,
    Preadditive.comp_add, Preadditive.add_comp]

end CochainComplex
