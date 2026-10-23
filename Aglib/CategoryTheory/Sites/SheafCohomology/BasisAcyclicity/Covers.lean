/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechFamily
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Cofinal selected covers of basis objects

The selected families refine every covering sieve, not just one distinguished
cover. Cover indices are independent of the universe of site objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe c h w

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)

/-- A cofinal supply of covering families on specified objects. This records
only topology and finite-intersection closure, not any cohomological conclusion. -/
structure CoverBasis [∀ W : C, HasFiniteProducts (Over W)] where
  /-- The objects on which acyclicity will be proved. -/
  objects : C → Prop
  /-- The selected families, with their actual arrows to the base. -/
  selected : ∀ (W : C) (ι : Type w), (ι → Over W) → Prop
  /-- Selected families are covering in the original topology. -/
  covering : ∀ {W ι U}, selected W ι U →
    Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W
  /-- Every covering sieve on a basis object contains a selected family. -/
  cofinal : ∀ (W : C), objects W → ∀ (R : Sieve W), R ∈ J W →
    ∃ (ι : Type w) (U : ι → Over W), selected W ι U ∧ ∀ i, R (U i).hom
  /-- All nonempty finite intersections in each selected family stay on the basis. -/
  intersections : ∀ {W ι U}, selected W ι U → ∀ (n : ℕ) (a : Fin (n + 1) → ι),
    objects (∏ᶜ fun i => U (a i)).left

variable {J} {W : C} {ι : Type w} (U : ι → Over W)

/-- A genuine covering family induces a locally surjective map from its
coproduct of representables to the represented base. -/
theorem familyMap_locallySurjective
    (hU : Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W) :
    Presheaf.IsLocallySurjective J (Presheaf.Cech.familyMap U) where
  imageSieve_mem {X} y := by
    apply J.superset_covering _ (J.pullback_stable y.down hU)
    intro V f hf
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
    refine ⟨⟨i, a⟩, ?_⟩
    apply ULift.ext
    exact ha.symm

end CategoryTheory.Sheaf.BasisAcyclicity
