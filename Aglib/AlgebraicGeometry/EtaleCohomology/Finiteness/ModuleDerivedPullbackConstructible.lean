/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.RingedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactBounds
public import Aglib.Algebra.Homology.DerivedCategory.Plus.BoundedIso

/-! # Original derived inverse images retain constructibility and intrinsic bounds -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original bounded constructible property is invariant under original isomorphisms. -/
theorem moduleBoundedConstructibleCohomologyPlus_iff_of_iso
    (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    {K L : DerivedCategory.Plus (ModuleSheaf X Λ)} (e : K ≅ L) :
    moduleBoundedConstructibleCohomologyPlus X Λ K ↔
      moduleBoundedConstructibleCohomologyPlus X Λ L := by
  suffices h : ∀ {K L : DerivedCategory.Plus (ModuleSheaf X Λ)}, (K ≅ L) →
      moduleBoundedConstructibleCohomologyPlus X Λ K →
        moduleBoundedConstructibleCohomologyPlus X Λ L from ⟨h e, h e.symm⟩
  intro K L e hK
  refine ⟨fun i => (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence X Λ).inverse.mapIso
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).mapIso e))).mp (hK.1 i), ?_⟩
  exact (DerivedCategory.Plus.exists_bounds_iff_of_iso e).mp hK.2

/-- Exact original inverse image preserves both homology constructibility and its bounds. -/
theorem moduleDerivedInverseImage_boundedConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf S Λ))
    (hK : moduleBoundedConstructibleCohomologyPlus S Λ K) :
    moduleBoundedConstructibleCohomologyPlus X Λ
      ((moduleDerivedInverseImage Λ f).obj K) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence X Λ).inverse.mapIso
        (((moduleInverseImage f Λ).rightDerivedFunctorPlusHomologyIso i).app K))).mpr
      (moduleIsConstructible_inverseImage Λ f _ (hK.1 i))
  · obtain ⟨a, b, ha, hb⟩ := hK.2
    let : K.IsGE a := ha
    let : K.IsLE b := hb
    exact ⟨a, b, (moduleInverseImage f Λ).rightDerivedFunctorPlus_isGE K a,
      (moduleInverseImage f Λ).rightDerivedFunctorPlus_isLE_of_preservesHomology K b⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
