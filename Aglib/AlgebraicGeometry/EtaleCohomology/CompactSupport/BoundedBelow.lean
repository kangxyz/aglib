/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.HigherDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSections

/-! # Bounded-below compactly supported cohomology over a field

For an admitted separated finite-type structure morphism to the field spectrum,
apply the existing chosen exceptional functor and then actual derived module
global sections. This is not the exceptional image alone. No assertion about
geometric stalks, scalar change, or unbounded cohomology is implicit here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wΛ

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
  (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of k)) Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification a).Xbar Λ)]

/-- Actual bounded-below `RΓ_c` for the admitted structure morphism. -/
def moduleCompactlySupportedCohomologyPlus :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  moduleExceptionalDirectImagePlus a Λ ⋙ moduleDerivedGlobalSections (Spec (.of k)) Λ

/-- Compactly supported cohomology of single torsion coefficients, as actual modules. -/
def moduleCompactlySupportedCohomology (q : ℤ) :
    (moduleTorsionCoefficients X Λ).FullSubcategory ⥤ ModuleCat.{u + 1} Λ :=
  moduleTorsionSingle X Λ 0 ⋙ moduleCompactlySupportedCohomologyPlus a Λ ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification a,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The compactification comparison retains the original derived-section image. -/
def moduleCompactlySupportedCohomologyPlusIso (C : Hom.DenseCompactification a) :
    moduleCompactlySupportedCohomologyPlus a Λ ≅
      moduleCompactificationFunctor a Λ C ⋙ moduleDerivedGlobalSections (Spec (.of k)) Λ :=
  Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusIso a Λ C)
    (moduleDerivedGlobalSections (Spec (.of k)) Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
