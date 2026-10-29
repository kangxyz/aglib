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
# Frozen R4 cancellation and reflection diagnostics

These conditional probes isolate specialization of the existing cancellation and reflection steps.
Diagnostic results remain separate from production validation on current native sources.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhaseAssembly

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

private theorem mapped_isIso_of_mateCube
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
    [IsIso (μ'.app (QB.obj K))] : IsIso (QC.map (μ.app K)) := by
  have ht : IsIso (γ.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.app (H.obj K)) := by
    rw [← h K]
    infer_instance
  have hr : IsIso (QC.map (μ.app K) ≫ b₂.app (H.obj K)) :=
    (isIso_comp_left_iff (γ.app (R₁.obj K)) _).mp ht
  exact (isIso_comp_right_iff _ (b₂.app (H.obj K))).mp hr

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

section Coupled

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

/-- Diagnostic only: specialize the current cancellation helper with its facts supplied. -/
theorem assemblyFromGivenFacts (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (hA : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)))
    (hU : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  let : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)) := hA
  let : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms := hU
  exact isIso_app_of_mateCube hCube K

/-- Diagnostic only: test mapped cancellation before reflection. -/
theorem mappedFromGivenFacts (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (hA : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K))) :
    IsIso ((moduleDerivedUnderlying Λ S').map
      ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) := by
  let : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)) := hA
  exact mapped_isIso_of_mateCube hCube K

end Coupled

section ReflectionOnly

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Diagnostic only: test the final reflection with the mapped isomorphism supplied. -/
theorem reflectionFromGivenFact (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hMapped : IsIso ((moduleDerivedUnderlying Λ S').map
      ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)))
    (hU : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  let : IsIso ((moduleDerivedUnderlying Λ S').map
      ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) := hMapped
  let : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms := hU
  exact isIso_of_reflects_iso _ (moduleDerivedUnderlying Λ S')

end ReflectionOnly

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhaseAssembly
