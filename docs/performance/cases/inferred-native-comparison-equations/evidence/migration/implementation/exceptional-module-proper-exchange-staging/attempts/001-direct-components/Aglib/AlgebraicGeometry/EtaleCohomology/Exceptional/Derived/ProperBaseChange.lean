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
# Proper base change for the original bounded-below module exchange

The original abelian proper exchange on internally torsion homology, the exact
torsion comparison for scalar forgetting, and the original mate-cube equation
imply invertibility of the same module-derived exchange component. The four
module-derived categories remain independently supplied. Each auxiliary abelian
derived category is selected once inside the proof by its standard realization.
The coefficient ring is arbitrary, and no common annihilator is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wMX wMS wMX' wMS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Proper base change makes the original module-derived exchange component
invertible on the actual bounded-below torsion-cohomology range. The proof-only
abelian derived realizations impose no additional choice on the statement. -/
theorem properModuleDerivedBaseChange_isIso_of_torsion_homology
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  let : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms :=
    Functor.rightDerivedFunctorPlus_reflectsIsomorphisms
      (SheafOfModules.toSheaf (constantRing S' Λ))
  let : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)) :=
    properDerivedBaseChange_isIso_of_torsion_homology f f' g g' sq
      ((moduleDerivedUnderlying Λ X).obj K)
      ((moduleTorsionCohomologyPlus_iff_underlying X Λ K).mp hK)
  have hcube := moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K
  have ht : IsIso
      ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
          ((moduleDerivedDirectImage Λ f).obj K) ≫
        (moduleDerivedUnderlying Λ S').map
          ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
        (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
          ((moduleDerivedInverseImage Λ g').obj K)) := by
    rw [← hcube]
    infer_instance
  have hr : IsIso
      ((moduleDerivedUnderlying Λ S').map
          ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) ≫
        (moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
          ((moduleDerivedInverseImage Λ g').obj K)) :=
    (isIso_comp_left_iff
      ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K)) _).mp ht
  have : IsIso ((moduleDerivedUnderlying Λ S').map
      ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) :=
    (isIso_comp_right_iff _
      ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K))).mp hr
  exact isIso_of_reflects_iso _ (moduleDerivedUnderlying Λ S')

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
