/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Pi.Abelian
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite object support in a family of abelian categories is a Serre property; its coordinate
functors are exact.

Source: `lean/R5Lab/Aglib/CategoryTheory/Pi/FiniteSupport.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `07d6017602c7f8b38293ff7b7cb832692f482c6342b86a1d304b0257c53bce40`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi
universe u v w
variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

/-- Finite nonzero support in a family of actual abelian categories. -/
def finiteObjectSupport : ObjectProperty (∀ i, C i) :=
  fun M => {i | ¬ IsZero (M i)}.Finite

abbrev FiniteCategoryFamily := (finiteObjectSupport C).FullSubcategory

instance finiteObjectSupport_serre : (finiteObjectSupport C).IsSerreClass where
  exists_zero := by
    obtain ⟨Z, hz⟩ := HasZeroObject.zero (C := ∀ i, C i)
    refine ⟨Z, hz, ?_⟩
    change {i | ¬ IsZero (Z i)}.Finite
    convert Set.finite_empty
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact (Pi.eval C i).map_isZero hz
  prop_of_mono f hf h := by
    let := hf
    let : ∀ i, Mono (f i) := fun i => (Pi.eval _ i).map_mono f
    apply h.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_mono (IsZero (C := C i)) (f i) hz)
  prop_of_epi f hf h := by
    let := hf
    let : ∀ i, Epi (f i) := fun i => (Pi.eval _ i).map_epi f
    apply h.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_epi (IsZero (C := C i)) (f i) hz)
  prop_X₂_of_shortExact h h₁ h₃ := by
    apply (h₁.union h₃).subset
    intro i hi
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact hi ((h.map_of_exact (Pi.eval C i)).exact.isZero_of_both_isZero hn.1 hn.2)

instance finiteCategoryFamily_abelian : Abelian (FiniteCategoryFamily C) := inferInstance

def finiteCategoryEvaluation (i : I) : CategoryTheory.ExactCategory.ExactFunctor
    (abelianExactStructure (FiniteCategoryFamily C)) (abelianExactStructure (C i)) where
  toFunctor := (finiteObjectSupport C).ι ⋙ Pi.eval C i
  map_conflation S h :=
    ((ObjectProperty.exactInclusion (finiteObjectSupport C)).map_conflation S h).map_of_exact
      (Pi.eval C i)

end CategoryTheory.Pi
