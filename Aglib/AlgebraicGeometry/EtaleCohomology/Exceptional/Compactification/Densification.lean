/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange

/-!
# The actual closed densification comparison

The original proper-refinement unit, pushed to the base through the original
composition isomorphism, identifies a raw compactification with its schematic
densification on native torsion inputs. No density is presumed after base change.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD

variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) [QuasiCompact C.j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]

/-- The actual unit-induced map from a raw compactification to its densification. -/
def moduleCompactificationDensificationMap :
    moduleRawCompactificationFunctor C Λ ⟶
      moduleRawCompactificationFunctor (Hom.Compactification.densify C).toCompactification Λ :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (imageComparison
      (moduleDerivedProperRefinementComparison (Hom.Compactification.densify C).j C.j
        (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C) Λ)
      (moduleDerivedDirectImageOverIso Λ (Hom.Compactification.densify C).p C.p
        (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C)))

/-- Invertibility is inherited from the same proper-refinement unit component. -/
instance moduleCompactificationDensificationMap_isIso :
    IsIso (moduleCompactificationDensificationMap C Λ) := by
  have (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
      IsIso ((moduleCompactificationDensificationMap C Λ).app K) := by
    let := moduleDerivedProperRefinementComparison_isIso
      (Hom.Compactification.densify C).j C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.isPullback_densify C) Λ K.obj K.property
    exact imageComparison_isIso_app _ _ K.obj
  exact NatIso.isIso_of_isIso_app _

/-- The raw and actual dense compactification models are canonically isomorphic. -/
def moduleCompactificationDensificationIso :
    moduleRawCompactificationFunctor C Λ ≅
      moduleRawCompactificationFunctor (Hom.Compactification.densify C).toCompactification Λ :=
  asIso (moduleCompactificationDensificationMap C Λ)

/-- This isomorphism retains the original densification map, not a replacement. -/
theorem moduleCompactificationDensificationIso_hom :
    (moduleCompactificationDensificationIso C Λ).hom =
      moduleCompactificationDensificationMap C Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
