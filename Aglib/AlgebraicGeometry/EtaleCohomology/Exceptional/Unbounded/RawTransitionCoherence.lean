/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition
public import Aglib.CategoryTheory.Functor.ImageComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage

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

/-- Original raw transitions compose contravariantly through the same actual
ambient composite, without a density assumption. -/
theorem moduleUnboundedRawCompactificationTransition_comp
    (E : Hom.Compactification f) (g : D.Xbar ⟶ E.Xbar)
    (sq' : IsPullback D.j (𝟙 X) g E.j) (hp' : g ≫ E.p = D.p)
    (sq'' : IsPullback C.j (𝟙 X) (h ≫ g) E.j) (hp'' : (h ≫ g) ≫ E.p = C.p)
    [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)] :
    moduleUnboundedRawCompactificationTransition C E (h ≫ g) sq'' hp'' Λ =
      moduleUnboundedRawCompactificationTransition D E g sq' hp' Λ ≫
        moduleUnboundedRawCompactificationTransition C D h sq hp Λ := by
  have hc := imageComparison_comp
    (moduleUnboundedDerivedProperRefinementComparison C.j D.j h sq Λ)
    (moduleUnboundedDerivedProperRefinementComparison D.j E.j g sq' Λ)
    (moduleUnboundedDerivedProperRefinementComparison C.j E.j (h ≫ g) sq'' Λ)
    (moduleUnboundedDerivedDirectImageCompIso Λ g h)
    (moduleUnboundedDerivedDirectImageOverIso Λ C.p D.p h hp)
    (moduleUnboundedDerivedDirectImageOverIso Λ D.p E.p g hp')
    (moduleUnboundedDerivedDirectImageOverIso Λ C.p E.p (h ≫ g) hp'')
    (moduleUnboundedDerivedProperRefinementComparison_comp C.j D.j E.j h g sq sq' sq'' Λ)
    (moduleUnboundedDerivedDirectImageOverIso_comp Λ C.p D.p E.p h g hp hp' hp'')
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
