/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomComplex.Precomposition

/-! # Native Hom-complex transport along a source isomorphism -/

@[expose] public noncomputable section

universe v u

open CategoryTheory

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} (I : CochainComplex C ℤ)

/-- The contravariant source isomorphism uses the original precomposition maps. -/
def precompIso (e : K ≅ L) : HomComplex L I ≅ HomComplex K I where
  hom := precompMap e.hom I
  inv := precompMap e.inv I
  hom_inv_id := by rw [← precompMap_comp, e.inv_hom_id, precompMap_id]
  inv_hom_id := by rw [← precompMap_comp, e.hom_inv_id, precompMap_id]

lemma acyclic_of_source_iso (e : K ≅ L) (h : (HomComplex L I).Acyclic) :
    (HomComplex K I).Acyclic := fun n => (h n).of_iso (precompIso I e)

end CochainComplex.HomComplex
