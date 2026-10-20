/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Actual cone isomorphisms from commuting squares

The original cone maps of a commuting square and its inverse give an actual cochain
isomorphism. Both maps remain the existing mappingCone.map construction.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/MappingCone/Iso.lean` from the supplied
frozen Quillen snapshot.
SHA-256: `ce096771edc6c4217873eb9931c3056334f068ad28a0f927d053ae5722e34270`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace CochainComplex.mappingCone
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}

/-- The actual cone maps induced by an isomorphism of commuting squares form a cochain
isomorphism. -/
def isoOfIso (d : K₁ ⟶ L₁) (e : K₂ ⟶ L₂) (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
    (comm : d ≫ b.hom = a.hom ≫ e) : mappingCone d ≅ mappingCone e := by
  have invComm : e ≫ b.inv = a.inv ≫ d := by
    calc
      e ≫ b.inv = a.inv ≫ (a.hom ≫ e) ≫ b.inv := by simp
      _ = a.inv ≫ (d ≫ b.hom) ≫ b.inv := by rw [comm]
      _ = a.inv ≫ d := by simp
  exact {
    hom := map d e a.hom b.hom comm
    inv := map e d a.inv b.inv invComm
    hom_inv_id := by rw [← map_comp]; simp only [Iso.hom_inv_id, map_id]
    inv_hom_id := by rw [← map_comp]; simp only [Iso.inv_hom_id, map_id] }

end CochainComplex.mappingCone
