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

private theorem isIso_of_inferred_component_equation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M N : C} {P A B Q : D} (β : M ⟶ N) {a : A ⟶ B}
    (u : P ⟶ A) (v : B ⟶ Q) (s : P ⟶ F.obj M) (t : F.obj N ⟶ Q)
    (h : u ≫ a ≫ v = s ≫ F.map β ≫ t)
    (ha : IsIso a) (hu : IsIso u) (hv : IsIso v)
    (hs : IsIso s) (ht : IsIso t) (hF : F.ReflectsIsomorphisms) : IsIso β := by
  let : IsIso a := ha
  let : IsIso u := hu
  let : IsIso v := hv
  let : IsIso s := hs
  let : IsIso t := ht
  let : F.ReflectsIsomorphisms := hF
  have hc : IsIso (s ≫ F.map β ≫ t) := by
    rw [← h]
    infer_instance
  have hr : IsIso (F.map β ≫ t) := (isIso_comp_left_iff s _).mp hc
  have : IsIso (F.map β) := (isIso_comp_right_iff _ t).mp hr
  exact isIso_of_reflects_iso β F

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

private theorem moduleExchange_isIso_of_torsion_homology
    [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  -- Keep the producer's inferred equation and its native category parameters intact.
  have hcube := moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K
  refine isIso_of_inferred_component_equation (moduleDerivedUnderlying Λ S')
    ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)
    ((derivedInverseImage g).map ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app K))
    ((derivedDirectImage f').map ((moduleDerivedInverseImageUnderlyingIso Λ g').inv.app K))
    ((moduleDerivedInverseImageUnderlyingIso Λ g).inv.app
      ((moduleDerivedDirectImage Λ f).obj K))
    ((moduleDerivedDirectImageUnderlyingIso Λ f').hom.app
      ((moduleDerivedInverseImage Λ g').obj K)) hcube ?_ ?_ ?_ ?_ ?_ ?_
  · apply properDerivedBaseChange_isIso_of_torsion_homology f f' g g' sq
    exact (moduleTorsionCohomologyPlus_iff_underlying X Λ K).mp hK
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · exact Functor.rightDerivedFunctorPlus_reflectsIsomorphisms
      (SheafOfModules.toSheaf (constantRing S' Λ))

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
  exact moduleExchange_isIso_of_torsion_homology Λ f f' g g' sq K hK

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
