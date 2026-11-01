/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.CategoryTheory.Functor.ComparisonPasting

/-!
# The original derived-unit comparison for a compactification refinement

The genuine Cartesian open square supplies the actual pullback comparison.
The refinement transformation is the original derived unit followed by its
image. Construction needs no proper-base-change theorem. Its invertibility
and full refinement coherence are separate obligations, not hypotheses hidden
inside a comparison package.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w₁ w₂

section ProperRefinement

variable {X Y₁ Y₂ : Scheme.{u}} (j₁ : X ⟶ Y₁) (j₂ : X ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : Y₁ ⟶ Y₂)
  (sq : IsPullback j₁ (𝟙 X) h j₂)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf Y₂ Λ)]

/-- The actual bounded-below pullback comparison above the original common open. -/
def moduleDerivedProperRefinementPullbackIso :
    moduleDerivedLowerShriek j₂ Λ ⋙ moduleDerivedInverseImage Λ h ≅
      moduleDerivedLowerShriek j₁ Λ :=
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (moduleLowerShriek j₂ Λ) (moduleInverseImage h Λ)).symm ≪≫
    Functor.rightDerivedFunctorPlusIso
      (moduleLowerShriek j₂ Λ ⋙ moduleInverseImage h Λ)
      (moduleLowerShriekCartesianIdentityIso j₁ j₂ h
        sq.flip Λ)

/-- The original derived unit induces the genuine compactification-refinement map. -/
def moduleDerivedProperRefinementComparison :
    moduleDerivedLowerShriek j₂ Λ ⟶
      moduleDerivedLowerShriek j₁ Λ ⋙ moduleDerivedDirectImage Λ h :=
  (Functor.rightUnitor (moduleDerivedLowerShriek j₂ Λ)).inv ≫
    Functor.comparisonPasting (moduleDerivedAdjunction Λ h).unit
      (moduleDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom

/-- Every component retains the original derived adjunction unit, not a chosen isomorphism. -/
theorem moduleDerivedProperRefinementComparison_app (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K =
      (moduleDerivedAdjunction Λ h).unit.app ((moduleDerivedLowerShriek j₂ Λ).obj K) ≫
        (moduleDerivedDirectImage Λ h).map
          ((moduleDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom.app K) := by
  simp [moduleDerivedProperRefinementComparison]

end ProperRefinement

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]

/-- The actual bounded-below pullback comparison above the original common open. -/
def moduleDerivedRefinementPullbackIso :
    moduleDerivedLowerShriek D.j Λ ⋙ moduleDerivedInverseImage Λ a.hom ≅
      moduleDerivedLowerShriek C.j Λ :=
  moduleDerivedProperRefinementPullbackIso C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ

/-- The original derived unit induces the genuine compactification-refinement map. -/
def moduleDerivedRefinementComparison :
    moduleDerivedLowerShriek D.j Λ ⟶
      moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ a.hom :=
  moduleDerivedProperRefinementComparison C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ

/-- Every component retains the original derived adjunction unit, not a chosen isomorphism. -/
theorem moduleDerivedRefinementComparison_app (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedRefinementComparison a Λ).app K =
      (moduleDerivedAdjunction Λ a.hom).unit.app ((moduleDerivedLowerShriek D.j Λ).obj K) ≫
        (moduleDerivedDirectImage Λ a.hom).map
          ((moduleDerivedRefinementPullbackIso a Λ).hom.app K) := by
  exact moduleDerivedProperRefinementComparison_app C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ K

/-- The general original-unit comparison has the literal original dense specialization. -/
theorem moduleDerivedProperRefinementComparison_dense :
    moduleDerivedProperRefinementComparison C.j D.j a.hom
      (Hom.DenseCompactification.isPullback_open a) Λ =
      moduleDerivedRefinementComparison a Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
