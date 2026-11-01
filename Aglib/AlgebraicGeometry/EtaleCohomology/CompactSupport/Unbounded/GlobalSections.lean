/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSections
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Comparison

/-! # Actual unbounded module global sections

Use the constructed Grothendieck K-injective replacement to right derive the
original module global-section functor on the existing derived categories.
The bounded-below comparison is characterized by its original localization units.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wΛ

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]

/-- The original module sections functor genuinely right derived on all native complexes. -/
abbrev moduleUnboundedDerivedGlobalSections :
    DerivedCategory (ModuleSheaf X Λ) ⥤ DerivedCategory (ModuleCat.{u + 1} Λ) :=
  (moduleGlobalSections X Λ).unboundedRightDerivedFunctor

/-- The original universal localization unit, not an objectwise surrogate. -/
abbrev moduleUnboundedDerivedGlobalSectionsUnit :
    (moduleGlobalSections X Λ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ moduleUnboundedDerivedGlobalSections X Λ :=
  (moduleGlobalSections X Λ).unboundedRightDerivedFunctorUnit

/-- Native bounded-below compatibility retaining the installed original units. -/
abbrev moduleUnboundedDerivedGlobalSectionsPlusIso :
    moduleDerivedGlobalSections X Λ ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ moduleUnboundedDerivedGlobalSections X Λ :=
  (moduleGlobalSections X Λ).unboundedRightDerivedFunctorPlusIso

/-- The comparison has the actual original bounded and unbounded unit equation. -/
@[reassoc]
theorem moduleUnboundedDerivedGlobalSectionsPlusIso_unit_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedCategory.Plus.ι.map ((moduleGlobalSections X Λ).rightDerivedFunctorPlusUnit.app K) ≫
        (moduleUnboundedDerivedGlobalSectionsPlusIso X Λ).hom.app (DerivedCategory.Plus.Q.obj K) =
      (moduleUnboundedDerivedGlobalSectionsUnit X Λ).app K.obj :=
  (moduleGlobalSections X Λ).unboundedRightDerivedFunctorPlusIso_unit_app K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
