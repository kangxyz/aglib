/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open

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
  (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (moduleLowerShriek D.j Λ) (moduleInverseImage a.hom Λ)).symm ≪≫
    Functor.rightDerivedFunctorPlusIso
      (moduleLowerShriek D.j Λ ⋙ moduleInverseImage a.hom Λ)
      (moduleLowerShriekCartesianIdentityIso C.j D.j a.hom
        (Hom.DenseCompactification.isPullback_open a).flip Λ)

/-- The original derived unit induces the genuine compactification-refinement map. -/
def moduleDerivedRefinementComparison :
    moduleDerivedLowerShriek D.j Λ ⟶
      moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ a.hom :=
  (Functor.rightUnitor (moduleDerivedLowerShriek D.j Λ)).inv ≫
    Functor.whiskerLeft (moduleDerivedLowerShriek D.j Λ)
      (moduleDerivedAdjunction Λ a.hom).unit ≫
    (Functor.associator (moduleDerivedLowerShriek D.j Λ)
      (moduleDerivedInverseImage Λ a.hom) (moduleDerivedDirectImage Λ a.hom)).inv ≫
    Functor.whiskerRight (moduleDerivedRefinementPullbackIso a Λ).hom
      (moduleDerivedDirectImage Λ a.hom)

/-- Every component retains the original derived adjunction unit, not a chosen isomorphism. -/
theorem moduleDerivedRefinementComparison_app (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedRefinementComparison a Λ).app K =
      (moduleDerivedAdjunction Λ a.hom).unit.app ((moduleDerivedLowerShriek D.j Λ).obj K) ≫
        (moduleDerivedDirectImage Λ a.hom).map
          ((moduleDerivedRefinementPullbackIso a Λ).hom.app K) := by
  simp [moduleDerivedRefinementComparison]

end AlgebraicGeometry.Scheme.EtaleCohomology
