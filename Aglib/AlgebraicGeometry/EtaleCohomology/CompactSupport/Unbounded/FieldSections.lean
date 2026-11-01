/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSections
public import Aglib.Algebra.Homology.DerivedCategory.ExactFunctorHomology

/-! # Actual unbounded sections over a separably closed field

Exactness is the proved module-linear terminal-germ/point-fibre theorem.
Uniqueness of right-derived functors compares the original unbounded universal
unit to the exact localization factor on all complexes, not only on D+.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wS wΛ

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of Ω)) Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]

local instance fieldExactSections_isRightDerivedFunctor :
    (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategory.IsRightDerivedFunctor
      (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (ModuleSheaf (Spec (.of Ω)) Λ) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryFactors

/-- The actual unbounded derived sections equal the original exact localization
through their specified original universal units. -/
def moduleUnboundedFieldSectionsExactIso :
    moduleUnboundedDerivedGlobalSections (Spec (.of Ω)) Λ ≅
      (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategory :=
  Functor.rightDerivedUnique _ _
    (moduleUnboundedDerivedGlobalSectionsUnit (Spec (.of Ω)) Λ)
    (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso (ModuleSheaf (Spec (.of Ω)) Λ) (.up ℤ))

/-- The comparison identifies the actual units on the entire unbounded complex category. -/
theorem moduleUnboundedFieldSectionsExactIso_unit :
    moduleUnboundedDerivedGlobalSectionsUnit (Spec (.of Ω)) Λ ≫
      Functor.whiskerLeft DerivedCategory.Q (moduleUnboundedFieldSectionsExactIso Ω Λ).hom =
        (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryFactors.inv := by
  change moduleUnboundedDerivedGlobalSectionsUnit (Spec (.of Ω)) Λ ≫
    Functor.whiskerLeft DerivedCategory.Q
      (Functor.rightDerivedNatTrans _ _
        (moduleUnboundedDerivedGlobalSectionsUnit (Spec (.of Ω)) Λ)
        (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryFactors.inv
        (HomologicalComplex.quasiIso (ModuleSheaf (Spec (.of Ω)) Λ) (.up ℤ)) (𝟙 _)) = _
  simp

/-- Original unbounded derived sections commute with native homology over this field. -/
def moduleUnboundedFieldSectionsHomologyIso (q : ℤ) :
    moduleUnboundedDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q ≅
      DerivedCategory.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q ⋙
        moduleGlobalSections (Spec (.of Ω)) Λ :=
  Functor.isoWhiskerRight (moduleUnboundedFieldSectionsExactIso Ω Λ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q) ≪≫
    (moduleGlobalSections (Spec (.of Ω)) Λ).mapDerivedCategoryHomologyIso q

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
