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
# Proposed source-typed evaluation of the original cube

Unrun diagnostic candidate. The original HasDerivedCategory binders precede
the local W choice. Only the two direct underlying-functor projections receive
explicit source and target category parameters. All functor and transformation
values remain the original constants.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

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

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Formation of the same equation, with the producer's module category parameters. -/
theorem pointwiseFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_h : (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        (@Functor.obj
          (DerivedCategory.Plus (ModuleSheaf X Λ)) inferInstance
          (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) inferInstance
          (moduleDerivedUnderlying Λ X) K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (@Functor.map
        (DerivedCategory.Plus (ModuleSheaf S' Λ)) inferInstance
        (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S')) inferInstance
        (moduleDerivedUnderlying Λ S') _ _
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K)) : True := True.intro

/-- The original whole cube, at the same K and the same six transformations. -/
theorem pointwiseValue (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K) ≫
      ((derivedBaseChangeMap f f' g g' sq.w.symm).app
        (@Functor.obj
          (DerivedCategory.Plus (ModuleSheaf X Λ)) inferInstance
          (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) inferInstance
          (moduleDerivedUnderlying Λ X) K)) ≫
      (derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K) =
    (moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      (@Functor.map
        (DerivedCategory.Plus (ModuleSheaf S' Λ)) inferInstance
        (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S')) inferInstance
        (moduleDerivedUnderlying Λ S') _ _
        ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K) :=
  moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PointwiseCube
