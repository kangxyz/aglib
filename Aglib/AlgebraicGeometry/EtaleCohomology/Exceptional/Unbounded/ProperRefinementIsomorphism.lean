/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementComparison
public import Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperBaseChangeTheorem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenClosedDetection
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Invertibility of the original non-dense proper-refinement comparison

Proper base change and the original mate-unit equation show that the original
unit is invertible on an open extension: on the open part its base change is
the unit of the identity, and on the complementary closed part its source is
zero. Joint open/closed detection then applies to this same unit. Composing
with the previously constructed open pullback isomorphism proves invertibility
of the unchanged refinement comparison, on every unbounded object over a torsion ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients


universe u w w₁ w₂ wZ

variable {X Y₁ Y₂ : Scheme.{u}} (j₁ : X ⟶ Y₁) (j₂ : X ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : Y₁ ⟶ Y₂) [IsProper h]
  (sq : IsPullback j₁ (𝟙 X) h j₂)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf Y₂ Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

include sq in
omit [IsOpenImmersion j₁] in
private theorem refinementUnit_open_isIso
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedInverseImage Λ j₂).map
      ((moduleUnboundedDerivedAdjunction Λ h).unit.app
        ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K))) := by
  let E := (moduleUnboundedDerivedLowerShriek j₂ Λ).obj K
  have hbc : IsIso ((moduleUnboundedDerivedBaseChangeMap Λ h (𝟙 X) j₂ j₁ sq.w.symm).app
      ((moduleUnboundedDerivedInverseImage Λ h).obj E)) := by
    let := Proper.properModuleUnboundedDerivedBaseChange_isIso
      Λ h (𝟙 X) j₂ j₁ sq N hN hΛ
    infer_instance
  let : (moduleUnboundedDerivedInverseImage Λ (𝟙 X)).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleUnboundedDerivedInverseImageIdIso Λ X).symm
  exact isIso_map_unit_of_iso_mate (moduleUnboundedDerivedAdjunction Λ h)
    (moduleUnboundedDerivedAdjunction Λ (𝟙 X))
    (moduleUnboundedDerivedInverseImageSquareIso Λ h (𝟙 X) j₂ j₁ sq.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ h (𝟙 X) j₂ j₁ sq.w.symm)
    rfl E hbc inferInstance

omit [IsOpenImmersion j₁] in
private theorem refinementUnit_closed_isIso
    {Z : Scheme.{u}} (i : Z ⟶ Y₂) [IsClosedImmersion i]
    (hcomp : Set.range j₂ = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedInverseImage Λ i).map
      ((moduleUnboundedDerivedAdjunction Λ h).unit.app
        ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K))) := by
  let E := (moduleUnboundedDerivedLowerShriek j₂ Λ).obj K
  let P := pullback h i
  let p : P ⟶ Z := pullback.snd h i
  let q : P ⟶ Y₁ := pullback.fst h i
  let := HasDerivedCategory.standard (ModuleSheaf P Λ)
  let sq : IsPullback q p h i := IsPullback.of_hasPullback h i
  have hbc : IsIso ((moduleUnboundedDerivedBaseChangeMap Λ h p i q sq.w.symm).app
      ((moduleUnboundedDerivedInverseImage Λ h).obj E)) := by
    let := Proper.properModuleUnboundedDerivedBaseChange_isIso
      Λ h p i q sq N hN hΛ
    infer_instance
  have hz : IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj E) :=
    isZero_moduleUnboundedDerivedInverseImage_lowerShriek j₂ Λ i hcomp K
  have hunit : IsIso ((moduleUnboundedDerivedAdjunction Λ p).unit.app
      ((moduleUnboundedDerivedInverseImage Λ i).obj E)) :=
    hz.isIso ((moduleUnboundedDerivedDirectImage Λ p).map_isZero
      ((moduleUnboundedDerivedInverseImage Λ p).map_isZero hz)) _
  exact isIso_map_unit_of_iso_mate (moduleUnboundedDerivedAdjunction Λ h)
    (moduleUnboundedDerivedAdjunction Λ p)
    (moduleUnboundedDerivedInverseImageSquareIso Λ h p i q sq.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ h p i q sq.w.symm) rfl E hbc hunit

/-- The original refinement comparison is invertible over the stated torsion ring,
using any actual complementary closed immersion for the target open. -/
theorem moduleUnboundedDerivedProperRefinementComparison_isIso_of_closedComplement
    {Z : Scheme.{u}} (i : Z ⟶ Y₂) [IsClosedImmersion i]
    (hcomp : Set.range j₂ = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K) := by
  have hopen := refinementUnit_open_isIso j₁ j₂ h sq Λ N hN hΛ K
  have hclosed := refinementUnit_closed_isIso j₂ h Λ N hN hΛ i hcomp K
  let : IsIso ((moduleUnboundedDerivedAdjunction Λ h).unit.app
      ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K)) :=
    moduleUnboundedDerived_isIso_of_open_closed j₂ Λ i hcomp
      ((moduleUnboundedDerivedAdjunction Λ h).unit.app
        ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K))
  rw [moduleUnboundedDerivedProperRefinementComparison_app]
  infer_instance

/-- Proper refinement preserves the original open extension by the original
unit comparison, for every unbounded object over the stated torsion ring. -/
theorem moduleUnboundedDerivedProperRefinementComparison_isIso
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K) := by
  let I := IdealSheafData.vanishingIdeal j₂.opensRange.compl
  let := HasDerivedCategory.standard (ModuleSheaf I.subscheme Λ)
  apply moduleUnboundedDerivedProperRefinementComparison_isIso_of_closedComplement
    j₁ j₂ h sq Λ N hN hΛ I.subschemeι
    (K := K)
  have hI : Set.range I.subschemeι = (Set.range j₂)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  exact ((congrArg (fun T : Set Y₂ => Tᶜ) hI).trans
    (compl_compl (Set.range j₂))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
