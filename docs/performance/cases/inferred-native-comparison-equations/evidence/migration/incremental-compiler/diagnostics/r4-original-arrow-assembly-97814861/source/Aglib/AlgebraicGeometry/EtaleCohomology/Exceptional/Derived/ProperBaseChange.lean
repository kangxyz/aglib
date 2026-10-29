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
# Frozen R4 original-arrow assembly diagnostic

The complete cancellation and reflection step keeps its categories, objects,
functor and supplied original arrow variable. The cube adapter evaluates the
existing cube only over variables. The thin native instance passes the literal
original exchange component, its reflexive value equality and the original facts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4OriginalArrowAssembly

open Coefficients

private theorem isIso_original_arrow_of_equation
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {M N : C} {P Q : D} (β : M ⟶ N)
    (s : P ⟶ F.obj M) (t : F.obj N ⟶ Q) (a : P ⟶ Q)
    [IsIso s] [IsIso t] [IsIso a] [F.ReflectsIsomorphisms]
    (h : a = s ≫ F.map β ≫ t) : IsIso β := by
  have ht : IsIso (s ≫ F.map β ≫ t) := by
    rw [← h]
    infer_instance
  have hr : IsIso (F.map β ≫ t) := (isIso_comp_left_iff s _).mp ht
  have : IsIso (F.map β) := (isIso_comp_right_iff _ t).mp hr
  exact isIso_of_reflects_iso β F

private theorem isIso_original_arrow_of_cube
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
    (β : G.obj (R₁.obj K) ⟶ R₂.obj (H.obj K)) (hβ : μ.app K = β)
    [IsIso (μ'.app (QB.obj K))] [QC.ReflectsIsomorphisms] : IsIso β := by
  apply isIso_original_arrow_of_equation QC β
    (γ.hom.app (R₁.obj K)) (b₂.hom.app (H.obj K))
    (G'.map (b₁.hom.app K) ≫ μ'.app (QB.obj K) ≫ R₂'.map (δ.hom.app K))
  simpa only [hβ] using h K

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

/-- Diagnostic only: retain the literal original arrow through the complete assembly. -/
theorem assemblyWithOriginalArrow (K : DerivedCategory.Plus (ModuleSheaf X Λ))
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
  exact isIso_original_arrow_of_cube
    (μ := moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm hCube K
    ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4OriginalArrowAssembly
