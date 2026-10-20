/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Pi.FiniteSupport
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Aglib.CategoryTheory.ExactCategory.Abelian

/-!
# Finite-support families of actual finite-length modules, their Serre property and exact
coordinate functors.

Source: `lean/R5Lab/Aglib/Algebra/Category/ModuleCat/FiniteLengthFamilies.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `a08af108d69dddc9863d9a9199849e0bc80f70ab29126f49dd8b31ed455663c9`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace ModuleCat.FiniteLengthFamilies
universe u v w
section Families
variable {I : Type u} (R : I → Type v) [∀ i, Ring (R i)]
abbrev AllFamilies := ∀ i, ModuleCat.{v} (R i)

/-- The generic finite-object-support property on the native module family. -/
abbrev finiteSupportProperty : ObjectProperty (AllFamilies R) :=
  CategoryTheory.Pi.finiteObjectSupport (fun i => ModuleCat.{v} (R i))

/-- Finite-support module families use the generic dependent category subcategory. -/
abbrev FiniteSupportFamily :=
  CategoryTheory.Pi.FiniteCategoryFamily (fun i => ModuleCat.{v} (R i))

/-- Actual finite-length modules, with finite nonzero support; morphisms are linear maps
in every coordinate. Nilpotent ring actions are retained. -/
def familyProperty : ObjectProperty (AllFamilies R) := fun M =>
  (∀ i, IsFiniteLength (R i) (M i)) ∧ {i | ¬ IsZero (M i)}.Finite

abbrev Family := (familyProperty R).FullSubcategory

local instance : Zero (AllFamilies R) := HasZeroObject.zero' (AllFamilies R)

instance familyProperty_serre : (familyProperty R).IsSerreClass where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_, ?_⟩
    · intro i
      have hz := (Pi.eval (fun i => ModuleCat.{v} (R i)) i).map_isZero
        (isZero_zero (AllFamilies R))
      have : Subsingleton ((0 : AllFamilies R) i) := ModuleCat.isZero_iff_subsingleton.mp hz
      exact .of_subsingleton
    · convert Set.finite_empty
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (Pi.eval (fun i => ModuleCat.{v} (R i)) i).map_isZero (isZero_zero _)
  prop_of_mono f hf h := by
    let := hf
    let : ∀ i, Mono (f i) := fun i => (Pi.eval _ i).map_mono f
    refine ⟨fun i => (h.1 i).of_injective
      ((ModuleCat.mono_iff_injective (f i)).mp inferInstance), ?_⟩
    apply h.2.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_mono (IsZero (C := ModuleCat (R i))) (f i) hz)
  prop_of_epi f hf h := by
    let := hf
    let : ∀ i, Epi (f i) := fun i => (Pi.eval _ i).map_epi f
    refine ⟨fun i => (h.1 i).of_surjective
      ((ModuleCat.epi_iff_surjective (f i)).mp inferInstance), ?_⟩
    apply h.2.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_epi (IsZero (C := ModuleCat (R i))) (f i) hz)
  prop_X₂_of_shortExact {S} h h₁ h₃ := by
    constructor
    · intro i
      have he := h.map_of_exact (Pi.eval (fun i => ModuleCat.{v} (R i)) i)
      obtain ⟨hn₁, ha₁⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp (h₁.1 i)
      obtain ⟨hn₃, ha₃⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp (h₃.1 i)
      let : IsNoetherian (R i) (S.X₁ i) := hn₁
      let : IsArtinian (R i) (S.X₁ i) := ha₁
      let : IsNoetherian (R i) (S.X₃ i) := hn₃
      let : IsArtinian (R i) (S.X₃ i) := ha₃
      exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_range_eq_ker (S.f i).hom (S.g i).hom he.exact.moduleCat_range_eq_ker,
          isArtinian_of_range_eq_ker (S.f i).hom (S.g i).hom he.exact.moduleCat_range_eq_ker⟩
    · apply (h₁.2.union h₃.2).subset
      intro i hi
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
      have he := h.map_of_exact (Pi.eval (fun i => ModuleCat.{v} (R i)) i)
      exact hi (he.exact.isZero_of_both_isZero hn.1 hn.2)

instance familyAbelian : Abelian (Family R) := inferInstance

/-- The actual family inclusion, carrying the componentwise exact structure. -/
def familyInclusion : CategoryTheory.ExactCategory.ExactFunctor
    (abelianExactStructure (Family R))
    (abelianExactStructure (AllFamilies R)) :=
  ObjectProperty.exactInclusion (familyProperty R)

/-- Projection to the actual local module is exact. -/
def evaluation (i : I) : CategoryTheory.ExactCategory.ExactFunctor
    (abelianExactStructure (Family R))
    (abelianExactStructure (ModuleCat.{v} (R i))) where
  toFunctor := (familyProperty R).ι ⋙ Pi.eval _ i
  map_conflation S h :=
    ((familyInclusion R).map_conflation S h).map_of_exact (Pi.eval _ i)

end Families
end ModuleCat.FiniteLengthFamilies
