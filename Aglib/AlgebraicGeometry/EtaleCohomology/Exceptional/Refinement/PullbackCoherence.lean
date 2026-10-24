/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.Comparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementComposition
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence

/-!
# Coherence of the original derived refinement pullback comparison

The actual ordinary Cartesian refinement comparison satisfies identity and
composition. The installed bounded-below derived composition comparisons
transport those equations to the existing derived pullback comparison. No
new comparison is chosen and no proper-base-change assertion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w₁ w₂ w₃

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

section Identity

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]

/-- The existing derived refinement pullback comparison has its original identity value. -/
theorem moduleDerivedRefinementPullbackIso_id :
    moduleDerivedRefinementPullbackIso (𝟙 C) Λ =
      Functor.isoWhiskerLeft (moduleDerivedLowerShriek C.j Λ)
        (moduleDerivedInverseImageIdIso Λ C.Xbar) ≪≫
      Functor.rightUnitor (moduleDerivedLowerShriek C.j Λ) := by
  exact Functor.rightDerivedFunctorPlusPullbackIso_id
    (moduleLowerShriek C.j Λ) (moduleInverseImage (𝟙 C.Xbar) Λ)
    (moduleLowerShriekCartesianIdentityIso C.j C.j (𝟙 C.Xbar)
      (Hom.DenseCompactification.isPullback_open (𝟙 C)).flip Λ)
    (moduleInverseImageIdIso Λ C.Xbar)
    (moduleLowerShriekCartesianIdentityIso_id C.j
      (Hom.DenseCompactification.isPullback_open (𝟙 C)).flip Λ)

end Identity

section Composition

variable {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E)
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{w₃} (ModuleSheaf E.Xbar Λ)]

/-- The existing derived pullback comparison respects composition of actual refinements. -/
theorem moduleDerivedRefinementPullbackIso_comp :
    moduleDerivedRefinementPullbackIso (a ≫ b) Λ =
      Functor.isoWhiskerLeft (moduleDerivedLowerShriek E.j Λ)
        (moduleDerivedInverseImageCompIso Λ b.hom a.hom) ≪≫
      (Functor.associator (moduleDerivedLowerShriek E.j Λ)
        (moduleDerivedInverseImage Λ b.hom) (moduleDerivedInverseImage Λ a.hom)).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedRefinementPullbackIso b Λ)
        (moduleDerivedInverseImage Λ a.hom) ≪≫
      moduleDerivedRefinementPullbackIso a Λ := by
  exact Functor.rightDerivedFunctorPlusPullbackIso_comp
    (moduleLowerShriek E.j Λ) (moduleInverseImage b.hom Λ) (moduleInverseImage a.hom Λ)
    (moduleLowerShriek D.j Λ) (moduleInverseImage (a.hom ≫ b.hom) Λ)
    (moduleLowerShriek C.j Λ)
    (moduleLowerShriekCartesianIdentityIso D.j E.j b.hom
      (Hom.DenseCompactification.isPullback_open b).flip Λ)
    (moduleLowerShriekCartesianIdentityIso C.j D.j a.hom
      (Hom.DenseCompactification.isPullback_open a).flip Λ)
    (moduleLowerShriekCartesianIdentityIso C.j E.j (a.hom ≫ b.hom)
      (Hom.DenseCompactification.isPullback_open (a ≫ b)).flip Λ)
    (moduleInverseImageCompIso Λ b.hom a.hom)
    (moduleLowerShriekCartesianIdentityIso_comp C.j D.j E.j b.hom a.hom
      (Hom.DenseCompactification.isPullback_open b).flip
      (Hom.DenseCompactification.isPullback_open a).flip
      (Hom.DenseCompactification.isPullback_open (a ≫ b)).flip Λ)

end Composition

end AlgebraicGeometry.Scheme.EtaleCohomology
