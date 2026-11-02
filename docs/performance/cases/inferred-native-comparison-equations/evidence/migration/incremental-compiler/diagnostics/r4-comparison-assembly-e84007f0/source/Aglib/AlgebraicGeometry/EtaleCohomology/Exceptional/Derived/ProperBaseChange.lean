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
# R4 concrete comparison boundary diagnostics

These probes distinguish supplied comparison facts from passing the same whole isomorphisms.
These frozen-context diagnostics do not alter the production theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComparisonAssembly

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

private theorem isIso_app_of_iso_cube
    {A B C D A' B' C' D' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* A'] [Category* B'] [Category* C'] [Category* D']
    {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
    {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
    (b₁ : R₁ ⋙ QA ≅ QB ⋙ R₁') (b₂ : R₂ ⋙ QC ≅ QD ⋙ R₂')
    {μ : R₁ ⋙ G ⟶ H ⋙ R₂} {μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂'}
    (γ : QA ⋙ G' ≅ G ⋙ QC) (δ : QB ⋙ H' ≅ H ⋙ QD)
    (h : HorizontalMateCubeEquation b₁.hom b₂.hom μ μ' γ.hom δ.hom) (K : B)
    [IsIso (μ'.app (QB.obj K))] [QC.ReflectsIsomorphisms] : IsIso (μ.app K) := by
  have ht : IsIso (γ.hom.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.hom.app (H.obj K)) := by
    rw [← h K]
    infer_instance
  have hr : IsIso (QC.map (μ.app K) ≫ b₂.hom.app (H.obj K)) :=
    (isIso_comp_left_iff (γ.hom.app (R₁.obj K)) _).mp ht
  have : IsIso (QC.map (μ.app K)) :=
    (isIso_comp_right_iff _ (b₂.hom.app (H.obj K))).mp hr
  exact isIso_of_reflects_iso (μ.app K) QC

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

/-- Diagnostic only: all existing comparison-isomorphism facts are supplied as parameters. -/
theorem assemblyWithAllFactsGiven (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (hA : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)))
    (hU : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms)
    (hb₁ : IsIso (moduleDerivedDirectImageUnderlyingIso Λ f).hom)
    (hb₂ : IsIso (moduleDerivedDirectImageUnderlyingIso Λ f').hom)
    (hγ : IsIso (moduleDerivedInverseImageUnderlyingIso Λ g).inv)
    (hδ : IsIso (moduleDerivedInverseImageUnderlyingIso Λ g').inv) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
  let : IsIso (moduleDerivedDirectImageUnderlyingIso Λ f).hom := hb₁
  let : IsIso (moduleDerivedDirectImageUnderlyingIso Λ f').hom := hb₂
  let : IsIso (moduleDerivedInverseImageUnderlyingIso Λ g).inv := hγ
  let : IsIso (moduleDerivedInverseImageUnderlyingIso Λ g').inv := hδ
  let : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K)) := hA
  let : (moduleDerivedUnderlying Λ S').ReflectsIsomorphisms := hU
  exact isIso_app_of_mateCube hCube K

/-- Diagnostic only: pass the four actual isomorphisms before taking their components. -/
theorem assemblyWithIsoInputs (K : DerivedCategory.Plus (ModuleSheaf X Λ))
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
  exact isIso_app_of_iso_cube
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm hCube K

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ComparisonAssembly
