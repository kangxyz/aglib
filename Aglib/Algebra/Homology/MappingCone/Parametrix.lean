/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Mapping-cone homotopies from specified parametrices

Original commuting squares and explicit reverse maps define actual homotopies
between their cone maps and the identity, hence a cone homotopy equivalence.
This construction is independent of module finiteness.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/MappingCone/Parametrix.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `fa7c7acdee1bc465b15383d3cba18a2b37f28d0487aeee8732c1fe68f4948779`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (d : K ⟶ L) (a : K ⟶ K) (b : L ⟶ L)
  (comm : d ≫ b = a ≫ d) (s : L ⟶ K)
  (ha : d ≫ s + a = 𝟙 K) (hb : s ≫ d + b = 𝟙 L)

/-- The specified reverse map supplies the actual cone homotopy of the diagonal square. -/
def mapHomotopyIdOfParametrix : Homotopy (𝟙 (mappingCone d)) (map d d a b comm) := by
  apply descHomotopy _ _ _ 0 ((Cochain.ofHom s).comp (inl d) (zero_add _))
  · simp only [δ_zero, zero_add, map, inl_desc, Cochain.comp_id]
    rw [← Cochain.comp_assoc, ← Cochain.ofHom_comp, ← Cochain.add_comp,
      ← Cochain.ofHom_add, ha] <;> simp
  · simp [map, δ_zero_cochain_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_add,
      ← Preadditive.add_comp, ← Category.assoc, hb]

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (d : K₁ ⟶ L₁) (e : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (c : K₂ ⟶ K₁) (q : L₂ ⟶ L₁)
  (hf : d ≫ b = a ≫ e) (hg : e ≫ q = c ≫ d)
  (s : L₁ ⟶ K₁) (t : L₂ ⟶ K₂)
  (hA : d ≫ s + a ≫ c = 𝟙 K₁) (hB : s ≫ d + b ≫ q = 𝟙 L₁)
  (hC : e ≫ t + c ≫ a = 𝟙 K₂) (hD : t ≫ e + q ≫ b = 𝟙 L₂)

/-- Original commuting squares and specified parametrices give an actual cone equivalence. -/
def homotopyEquivOfParametrices : HomotopyEquiv (mappingCone d) (mappingCone e) where
  hom := map d e a b hf
  inv := map e d c q hg
  homotopyHomInvId := by
    have h := (mapHomotopyIdOfParametrix d (a ≫ c) (b ≫ q)
      (by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]) s hA hB).symm
    rw [← map_comp d e d a b hf c q hg]
    exact h
  homotopyInvHomId := by
    have h := (mapHomotopyIdOfParametrix e (c ≫ a) (q ≫ b)
      (by rw [← Category.assoc, hg, Category.assoc, hf, Category.assoc]) t hC hD).symm
    rw [← map_comp e d e c q hg a b hf]
    exact h

end CochainComplex.mappingCone
