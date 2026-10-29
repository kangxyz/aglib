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
# Frozen R4 prerequisite-value diagnostics

These declarations isolate the existing torsion, proper exchange, conservativity and cube values.
Diagnostic results remain separate from production validation on current native sources.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhasePrelude

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

section Underlying

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]

/-- Isolated original torsion-transfer value, with the actual underlying object. -/
theorem torsionValue (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    ∀ n : ℤ, Sheaf.IsTorsion
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
        ((moduleDerivedUnderlying Λ X).obj K)) :=
  (moduleTorsionCohomologyPlus_iff_underlying X Λ K).mp hK

/-- Isolated original conservative functor value. -/
theorem reflectionValue : (moduleDerivedUnderlying Λ X).ReflectsIsomorphisms :=
  Functor.rightDerivedFunctorPlus_reflectsIsomorphisms
    (SheafOfModules.toSheaf (constantRing X Λ))

end Underlying

section ProperExchange

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Isolated original proper-exchange value using the unchanged torsion proof. -/
theorem abelianExchangeValue (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)) :=
  properDerivedBaseChange_isIso_of_torsion_homology f f' g g' sq
    ((moduleDerivedUnderlying Λ X).obj K)
    ((moduleTorsionCohomologyPlus_iff_underlying X Λ K).mp hK)

end ProperExchange

section Cube

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

/-- Isolated value of the same existing whole mate-cube equation. -/
theorem cubeValue : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv :=
  moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm

end Cube

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhasePrelude
