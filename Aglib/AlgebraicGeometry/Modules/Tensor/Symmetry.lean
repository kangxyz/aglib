/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalCoefficientFunctors.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[31, 48]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Functor CategoryTheory.BraidedCategory SheafOfModulesOfCommRing

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical sheaf tensor braiding for two arbitrary module sheaves. -/
def moduleTensorSymmetry (Z : Scheme.{u}) (M N : Z.Modules) :
    (moduleTensorLeftFunctor Z M).obj N ≅ (moduleTensorLeftFunctor Z N).obj M :=
  SheafOfModulesOfCommRing.tensorBraiding Z.sheaf M N

/-- The functorial comparison from right coefficient tensor to left coefficient tensor. -/
def moduleTensorRightLeftIso (X : Scheme.{u}) (M : X.Modules) :
    moduleTensorRightFunctor X M ≅ moduleTensorLeftFunctor X M :=
  Functor.isoWhiskerLeft (SheafOfModulesOfCommRing.toPresheaf X.sheaf)
    (Functor.isoWhiskerRight (tensorLeftIsoTensorRight
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M)).symm
          (SheafOfModulesOfCommRing.associatedSheaf X.sheaf))


/-- The functor comparison retains the original sheafified braiding on every component. -/
lemma moduleTensorRightLeftIso_hom_app (X : Scheme.{u}) (M N : X.Modules) :
    (moduleTensorRightLeftIso X M).hom.app N = (moduleTensorSymmetry X N M).hom := by
  rfl

/-- The original componentwise symmetry is the canonical right/left tensor comparison. -/
abbrev moduleTensorSymmetryNatIso (X : Scheme.{u}) (M : X.Modules) :
    moduleTensorRightFunctor X M ≅ moduleTensorLeftFunctor X M :=
  moduleTensorRightLeftIso X M

end AlgebraicGeometry.Scheme.Modules
