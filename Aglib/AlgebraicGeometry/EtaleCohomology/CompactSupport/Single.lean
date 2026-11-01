/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Original single coefficients in the bounded-below torsion category

The input property is internal torsion, not a uniform annihilator. The functor
is the original native single functor with its proven range restriction.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- A torsion coefficient has torsion native homology when placed in one degree. -/
theorem moduleSingle_torsion (M : ModuleSheaf X Λ) (hM : moduleIsTorsion X Λ M)
    (i : ℤ) : moduleTorsionCohomologyPlus X Λ
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) i).obj M) := by
  intro n
  by_cases hn : n = i
  · subst n
    exact moduleIsTorsion_of_iso X Λ
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleSheaf X Λ) i).app M) hM
  · have hz : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) n).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) i).obj M)) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ i n h
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ i n h
    let φ : ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) n).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) i).obj M)) ⟶ M := 0
    let mono : Mono ((SheafOfModules.toSheaf (constantRing X Λ)).map φ) :=
      ((SheafOfModules.toSheaf (constantRing X Λ)).map_isZero hz).mono _
    exact @Sheaf.IsTorsion.of_mono _ _ _ _ _ _ hM
      ((SheafOfModules.toSheaf (constantRing X Λ)).map φ) mono

/-- Internally torsion coefficients, as the native full subcategory. -/
def moduleTorsionCoefficients : ObjectProperty (ModuleSheaf X Λ) := moduleIsTorsion X Λ

/-- The original single functor restricted to torsion coefficients and torsion homology. -/
def moduleTorsionSingle (i : ℤ) :
    (moduleTorsionCoefficients X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  (moduleTorsionCohomologyPlus X Λ).lift
    ((moduleTorsionCoefficients X Λ).ι ⋙
      DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) i)
    (fun M => moduleSingle_torsion X Λ M.obj M.property i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
