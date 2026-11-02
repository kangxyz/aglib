/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFiber
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteEtaleRigidity
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClassification

/-! # Original H1 detection at the generic point

Actual extension of finite-etale generic-fibre maps supplies fullness, hence
injectivity of original H1 for finite locally constant coefficients. Integral
closedness of every actual stalk is retained explicitly. No closed-point DVR
criterion, classification premise, or alternative cohomology model is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]

/-- Restriction to the actual generic point detects original finite-coefficient H1. -/
theorem h1Pullback_injective_genericPoint
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Injective (h1Pullback (X.fromSpecStalk (genericPoint X)) F) :=
  FiniteEtaleRigidity.h1Pullback_injective_finite_of_full
    (X.fromSpecStalk (genericPoint X)) (stacks03AJ X) (stacks03RV X)
    (stacks03AJ (Spec X.functionField)) F hF

end AlgebraicGeometry.Scheme.EtaleCohomology
