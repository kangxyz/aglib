/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.Algebra.Homology.CochainComplexPlus.Single

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedFlatPullbackSingle.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 50]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Original flat pullback of single sheaves -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived category of module sheaves. -/
local instance flatSingleStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- The literal termwise comparison for pullback of the original single complex. -/
def pullbackSingleZeroPlusIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback f).mapCochainComplexPlus.obj
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus X.Modules 0).obj ((Scheme.Modules.pullback f).obj M) :=
  (CochainComplex.plus X.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pullback f) (.up ℤ) 0).app M)
/-- Actual flat pullback of a single sheaf via the original installed unit. -/
def derivedFlatPullbackPlusSingleIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (M : Y.Modules) :
    (derivedFlatPullbackPlus f).obj ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback f).obj M) := by
  have := isIso_derivedFlatPullbackPlusUnit f
  exact (asIso (((Scheme.Modules.pullback f).rightDerivedFunctorPlusUnit).app
    ((CochainComplex.singleFunctorPlus Y.Modules 0).obj M))).symm ≪≫
      DerivedCategory.Plus.Q.mapIso (pullbackSingleZeroPlusIso f M)
/-- The installed unit followed by the comparison is the original termwise single map. -/
theorem derivedFlatPullbackPlusSingleIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (M : Y.Modules) :
    (Scheme.Modules.pullback f).rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj M) ≫
      (derivedFlatPullbackPlusSingleIso f M).hom =
        DerivedCategory.Plus.Q.map (pullbackSingleZeroPlusIso f M).hom := by
  have := isIso_derivedFlatPullbackPlusUnit f
  dsimp only [derivedFlatPullbackPlusSingleIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, Functor.mapIso_hom]
  simp
end AlgebraicGeometry.Scheme.Modules
