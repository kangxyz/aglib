/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative

/-!
# R4 comparison-isomorphism instance diagnostics

These probes isolate the actual whole comparison-isomorphism proof values.
These frozen-context diagnostics do not alter the production theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComparisonValues

open Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S)

/-- The actual direct-image comparison supplies its whole isomorphism instance. -/
theorem directComparisonValue : IsIso (moduleDerivedDirectImageUnderlyingIso Λ f).hom := by
  infer_instance

/-- The actual inverse-image comparison supplies its inverse isomorphism instance. -/
theorem inverseComparisonValue : IsIso (moduleDerivedInverseImageUnderlyingIso Λ f).inv := by
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComparisonValues
