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

private theorem isIso_app_of_mateCube
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
    {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
    {b₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁'} {b₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂'}
    {μ : R₁ ⋙ G ⟶ H ⋙ R₂} {μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂'}
    {γ : QA ⋙ G' ⟶ G ⋙ QC} {δ : QB ⋙ H' ⟶ H ⋙ QD}
    (h : HorizontalMateCubeEquation b₁ b₂ μ μ' γ δ) (K : B)
    [IsIso b₁] [IsIso b₂] [IsIso γ] [IsIso δ]
    [IsIso (μ'.app (QB.obj K))] [QC.ReflectsIsomorphisms] : IsIso (μ.app K) := by
  have ht : IsIso (γ.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.app (H.obj K)) := by
    rw [← h K]
    infer_instance
  have hr : IsIso (QC.map (μ.app K) ≫ b₂.app (H.obj K)) :=
    (isIso_comp_left_iff (γ.app (R₁.obj K)) _).mp ht
  have : IsIso (QC.map (μ.app K)) :=
    (isIso_comp_right_iff _ (b₂.app (H.obj K))).mp hr
  exact isIso_of_reflects_iso (μ.app K) QC

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
  exact isIso_app_of_mateCube
    (moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm) K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
