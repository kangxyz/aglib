/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleFullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Module

/-! # The original module-linear stalk inside an open immersion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

variable (Λ : Type (u + 1)) [Ring Λ]

local instance moduleStalkInsideHasModuleLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- The geometric-point comparison on actual module-valued sheaves. -/
def moduleValuedStalkInverseImageIso :
    (pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      moduleValuedInverseImage f Λ ⋙ (pointSmallEtale η).sheafFiber :=
  geometricModuleStalkInverseImageIso f η Λ

/-- The original module-linear geometric stalk commutes with genuine native pullback. -/
def moduleStalkInverseImageIso :
    moduleGeometricStalk Λ (η ≫ f) ≅ moduleInverseImage f Λ ⋙ moduleGeometricStalk Λ η :=
  Functor.isoWhiskerLeft _ (moduleValuedStalkInverseImageIso f η Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageValuedIso Λ f).symm _ ≪≫
    Functor.associator _ _ _

variable [IsOpenImmersion f]

/-- Inside the open, extension by zero has exactly the original module-linear stalk. -/
def moduleLowerShriekStalkIso :
    moduleLowerShriek f Λ ⋙ moduleGeometricStalk Λ (η ≫ f) ≅ moduleGeometricStalk Λ η :=
  Functor.isoWhiskerLeft _ (moduleStalkInverseImageIso f η Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekInverseImageIso f Λ) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.EtaleCohomology
