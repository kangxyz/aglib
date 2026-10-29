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
# Frozen original cube evaluation at K

These checks isolate formation and the actual value of the original component equation.
These are frozen-context diagnostics, not production theorem coverage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge
attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Faithful formation of the original typed pointwise cube equation. -/
theorem pointwiseFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_h : (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K)) : True := True.intro

/-- Evaluate the original whole cube at the same K, with every original component retained. -/
theorem pointwiseValue (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        ((moduleDerivedUnderlying Λ X).obj K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (moduleDerivedUnderlying Λ S').map
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K) :=
  moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube
