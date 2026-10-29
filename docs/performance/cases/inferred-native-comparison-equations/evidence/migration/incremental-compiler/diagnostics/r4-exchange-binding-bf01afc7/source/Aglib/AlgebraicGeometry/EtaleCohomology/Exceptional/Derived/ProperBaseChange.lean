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
# Frozen R4 exchange-value binding controls

The common original-arrow proof is unchanged. These controls distinguish the two
native exchange values and explicit binding of their already-specified functors.
The original supplied arrow and all chosen worlds remain unchanged; no result is
claimed for production R4 from a conditional diagnostic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ExchangeBinding

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

/-- Diagnostic: fix the module exchange only, with the abelian exchange variable. -/
theorem moduleExchangeFixed
    (μ' : derivedDirectImage f ⋙ derivedInverseImage g ⟶
      derivedInverseImage g' ⋙ derivedDirectImage f')
    (_hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm) μ'
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (β : (moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K) ⟶
      (moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj K))
    (_hβ : (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K = β)
    [IsIso (μ'.app ((moduleDerivedUnderlying Λ X).obj K))]
    [(moduleDerivedUnderlying Λ S').ReflectsIsomorphisms] : IsIso β := by
  exact isIso_original_arrow_of_cube
    (μ := (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm))
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm _hCube K β _hβ

/-- Diagnostic: fix the abelian exchange only, with the module exchange variable. -/
theorem abelianExchangeFixed
    (μ : moduleDerivedDirectImage Λ f ⋙ moduleDerivedInverseImage Λ g ⟶
      moduleDerivedInverseImage Λ g' ⋙ moduleDerivedDirectImage Λ f')
    (_hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      μ (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (β : (moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K) ⟶
      (moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj K))
    (_hβ : μ.app K = β)
    [IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app ((moduleDerivedUnderlying Λ X).obj K))]
    [(moduleDerivedUnderlying Λ S').ReflectsIsomorphisms] : IsIso β := by
  exact isIso_original_arrow_of_cube (μ := μ)
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm _hCube K β _hβ

/-- Diagnostic: bind both literal original exchange values explicitly. -/
theorem bothExchangesExplicit
    (_hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (β : (moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K) ⟶
      (moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj K))
    (_hβ : (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K = β)
    [IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app ((moduleDerivedUnderlying Λ X).obj K))]
    [(moduleDerivedUnderlying Λ S').ReflectsIsomorphisms] : IsIso β := by
  exact isIso_original_arrow_of_cube
    (μ := (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm))
    (μ' := (derivedBaseChangeMap f f' g g' sq.w.symm))
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm _hCube K β _hβ

/-- Diagnostic: also bind every already-specified native functor explicitly. -/
theorem nativeFunctorsExplicit
    (_hCube : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (β : (moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K) ⟶
      (moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj K))
    (_hβ : (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K = β)
    [IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app ((moduleDerivedUnderlying Λ X).obj K))]
    [(moduleDerivedUnderlying Λ S').ReflectsIsomorphisms] : IsIso β := by
  exact isIso_original_arrow_of_cube
    (R₁ := moduleDerivedDirectImage Λ f)
    (R₂ := moduleDerivedDirectImage Λ f')
    (R₁' := derivedDirectImage f)
    (R₂' := derivedDirectImage f')
    (G := moduleDerivedInverseImage Λ g)
    (H := moduleDerivedInverseImage Λ g')
    (G' := derivedInverseImage g)
    (H' := derivedInverseImage g')
    (QA := moduleDerivedUnderlying Λ S)
    (QB := moduleDerivedUnderlying Λ X)
    (QC := moduleDerivedUnderlying Λ S')
    (QD := moduleDerivedUnderlying Λ X')
    (μ := (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm))
    (μ' := (derivedBaseChangeMap f f' g g' sq.w.symm))
    (moduleDerivedDirectImageUnderlyingIso Λ f)
    (moduleDerivedDirectImageUnderlyingIso Λ f')
    (moduleDerivedInverseImageUnderlyingIso Λ g).symm
    (moduleDerivedInverseImageUnderlyingIso Λ g').symm _hCube K β _hβ

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4ExchangeBinding
