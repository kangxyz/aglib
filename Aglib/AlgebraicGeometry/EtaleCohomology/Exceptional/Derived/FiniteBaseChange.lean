/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DerivedBaseChange
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.MateCubeIsomorphism

/-!
# Finite base change for the original module-derived exchange

The original abelian finite-base-change theorem, the proved scalar-forgetting
exchange square, and conservativity of exact derived forgetting imply that the
same original module-derived exchange is invertible. The coefficient ring is
arbitrary. This is a finite-morphism consumer, not a general proper-base-change
theorem or an assertion of the full exceptional calculus.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Coefficients

universe u wMX wMS wMX' wMS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  [IsFinite f] (sq : IsPullback g' f' f g)

/-- Finite base change makes the same original native module-derived exchange
invertible, with arbitrary ring coefficients and independent derived universes. -/
theorem finiteModuleDerivedBaseChange_isIso :
    IsIso (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  let : IsIso (derivedBaseChangeMap f f' g g' sq.w.symm) :=
    finiteDerivedBaseChange_isIso f f' g g' sq
  exact (moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm).isIso

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
