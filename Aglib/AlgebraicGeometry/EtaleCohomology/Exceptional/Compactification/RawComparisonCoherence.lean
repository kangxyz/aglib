/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence

/-!
# Original transitions between raw compactification models

Actual Cartesian open refinements give the same unit-induced transition before
any density restriction. Their composition uses only the previously established
original unit and structural-image coherence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD wE

variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C D : Hom.Compactification f) (h : C.Xbar ⟶ D.Xbar)
  (sq : IsPullback C.j (𝟙 X) h D.j) (hp : h ≫ D.p = C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The original unit-induced transition for a specified raw refinement. -/
def moduleRawCompactificationTransition :
    moduleRawCompactificationFunctor D Λ ⟶ moduleRawCompactificationFunctor C Λ :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (imageComparison (moduleDerivedProperRefinementComparison C.j D.j h sq Λ)
      (moduleDerivedDirectImageOverIso Λ C.p D.p h hp))

/-- Original raw transitions compose contravariantly through the same actual
ambient composite, without a density assumption. -/
theorem moduleRawCompactificationTransition_comp
    (E : Hom.Compactification f) (g : D.Xbar ⟶ E.Xbar)
    (sq' : IsPullback D.j (𝟙 X) g E.j) (hp' : g ≫ E.p = D.p)
    (sq'' : IsPullback C.j (𝟙 X) (h ≫ g) E.j) (hp'' : (h ≫ g) ≫ E.p = C.p)
    [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)] :
    moduleRawCompactificationTransition C E (h ≫ g) sq'' hp'' Λ =
      moduleRawCompactificationTransition D E g sq' hp' Λ ≫
        moduleRawCompactificationTransition C D h sq hp Λ := by
  have hc := imageComparison_comp
    (moduleDerivedProperRefinementComparison C.j D.j h sq Λ)
    (moduleDerivedProperRefinementComparison D.j E.j g sq' Λ)
    (moduleDerivedProperRefinementComparison C.j E.j (h ≫ g) sq'' Λ)
    (moduleDerivedDirectImageCompIso Λ g h)
    (moduleDerivedDirectImageOverIso Λ C.p D.p h hp)
    (moduleDerivedDirectImageOverIso Λ D.p E.p g hp')
    (moduleDerivedDirectImageOverIso Λ C.p E.p (h ≫ g) hp'')
    (moduleDerivedProperRefinementComparison_comp C.j D.j E.j h g sq sq' sq'' Λ)
    (moduleDerivedDirectImageOverIso_comp Λ C.p D.p E.p h g hp hp' hp'')
  simpa only [moduleRawCompactificationTransition, moduleRawCompactificationFunctor,
    Functor.whiskerLeft_comp] using
    congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι) hc

end AlgebraicGeometry.Scheme.EtaleCohomology
