/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalGenerationEndpoints.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[39, 56], [66, 89]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived category of module sheaves used for single-object comparisons. -/
local instance singleComparisonStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- An additive functor commutes with forming the degree-zero bounded-below single complex. -/
def exactSingleComplexNatIso {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive] :
    CochainComplex.singleFunctorPlus X.Modules 0 ⋙ F.mapCochainComplexPlus ≅
      F ⋙ CochainComplex.singleFunctorPlus Y.Modules 0 :=
  NatIso.ofComponents (fun M => (CochainComplex.plus Y.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality f)

/-- The degree-zero single comparison for the right-derived functor of an additive functor
preserving homology. -/
def exactDerivedSingleNatIso {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] [F.PreservesHomology] :
    DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙ F.rightDerivedFunctorPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor Y.Modules 0 := by
  have := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact (isoWhiskerLeft (CochainComplex.singleFunctorPlus X.Modules 0)
      (asIso F.rightDerivedFunctorPlusUnit).symm) ≪≫
    isoWhiskerRight (exactSingleComplexNatIso F) DerivedCategory.Plus.Q

/-- The original right-derived unit comparison on degree-zero singles for an additive functor. -/
def rightDerivedSingleComparison {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    F ⋙ DerivedCategory.Plus.singleFunctor Y.Modules 0 ⟶
      DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙ F.rightDerivedFunctorPlus :=
  (isoWhiskerRight (exactSingleComplexNatIso F) DerivedCategory.Plus.Q).inv ≫
    whiskerLeft (CochainComplex.singleFunctorPlus X.Modules 0) F.rightDerivedFunctorPlusUnit

end AlgebraicGeometry.Scheme.Modules
