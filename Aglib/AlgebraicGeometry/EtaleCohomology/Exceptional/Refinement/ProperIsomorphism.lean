/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.DerivedDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.DerivedOpenClosed
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Invertibility of the original compactification-refinement comparison

Proper base change and the original mate-unit equation show that the original
unit is invertible on an open extension: on the open part its base change is
the unit of the identity, and on the complementary closed part its source is
zero. Joint open/closed detection then applies to this same unit. Composing
with the previously constructed open pullback isomorphism proves invertibility
of the unchanged refinement comparison, only on torsion cohomology.
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

include j₁ sq in
omit [IsProper h] in
private theorem refinementPullback_torsion
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    moduleTorsionCohomologyPlus Y₁ Λ
      ((moduleDerivedInverseImage Λ h).obj ((moduleDerivedLowerShriek j₂ Λ).obj K)) :=
  moduleTorsionCohomology_of_iso Y₁ Λ
    (DerivedCategory.Plus.ι.mapIso ((moduleDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).app K))
    (moduleDerivedLowerShriek_preservesTorsionCohomology j₁ Λ hK)

include j₁ sq in
omit [IsOpenImmersion j₁] in
private theorem refinementUnit_open_isIso
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hLE : moduleTorsionCohomologyPlus Y₁ Λ
      ((moduleDerivedInverseImage Λ h).obj ((moduleDerivedLowerShriek j₂ Λ).obj K))) :
    IsIso ((moduleDerivedInverseImage Λ j₂).map
      ((moduleDerivedAdjunction Λ h).unit.app ((moduleDerivedLowerShriek j₂ Λ).obj K))) := by
  let E := (moduleDerivedLowerShriek j₂ Λ).obj K
  have hbc : IsIso ((moduleDerivedBaseChangeMap Λ h (𝟙 X) j₂ j₁ sq.w.symm).app
      ((moduleDerivedInverseImage Λ h).obj E)) :=
    Proper.properModuleDerivedBaseChange_isIso_of_torsion_homology
      Λ h (𝟙 X) j₂ j₁ sq ((moduleDerivedInverseImage Λ h).obj E) hLE
  let : (moduleDerivedInverseImage Λ (𝟙 X)).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleDerivedInverseImageIdIso Λ X).symm
  exact isIso_map_unit_of_iso_mate (moduleDerivedAdjunction Λ h)
    (moduleDerivedAdjunction Λ (𝟙 X))
    (moduleDerivedInverseImageSquareIso Λ h (𝟙 X) j₂ j₁ sq.w.symm)
    (moduleDerivedBaseChangeMap Λ h (𝟙 X) j₂ j₁ sq.w.symm) rfl E hbc inferInstance

omit [IsOpenImmersion j₁] in
private theorem refinementUnit_closed_isIso
    {Z : Scheme.{u}} (i : Z ⟶ Y₂) [IsClosedImmersion i]
    (hcomp : Set.range j₂ = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hLE : moduleTorsionCohomologyPlus Y₁ Λ
      ((moduleDerivedInverseImage Λ h).obj ((moduleDerivedLowerShriek j₂ Λ).obj K))) :
    IsIso ((moduleDerivedInverseImage Λ i).map
      ((moduleDerivedAdjunction Λ h).unit.app ((moduleDerivedLowerShriek j₂ Λ).obj K))) := by
  let E := (moduleDerivedLowerShriek j₂ Λ).obj K
  let P := pullback h i
  let p : P ⟶ Z := pullback.snd h i
  let q : P ⟶ Y₁ := pullback.fst h i
  let := HasDerivedCategory.standard (ModuleSheaf P Λ)
  let sq : IsPullback q p h i := IsPullback.of_hasPullback h i
  have hbc : IsIso ((moduleDerivedBaseChangeMap Λ h p i q sq.w.symm).app
      ((moduleDerivedInverseImage Λ h).obj E)) :=
    Proper.properModuleDerivedBaseChange_isIso_of_torsion_homology
      Λ h p i q sq ((moduleDerivedInverseImage Λ h).obj E) hLE
  have hz : IsZero ((moduleDerivedInverseImage Λ i).obj E) :=
    isZero_moduleDerivedInverseImage_lowerShriek j₂ Λ i hcomp K
  have hunit : IsIso ((moduleDerivedAdjunction Λ p).unit.app
      ((moduleDerivedInverseImage Λ i).obj E)) :=
    hz.isIso ((moduleDerivedDirectImage Λ p).map_isZero
      ((moduleDerivedInverseImage Λ p).map_isZero hz)) _
  exact isIso_map_unit_of_iso_mate (moduleDerivedAdjunction Λ h)
    (moduleDerivedAdjunction Λ p)
    (moduleDerivedInverseImageSquareIso Λ h p i q sq.w.symm)
    (moduleDerivedBaseChangeMap Λ h p i q sq.w.symm) rfl E hbc hunit

/-- The original refinement comparison is invertible on torsion cohomology,
using any actual complementary closed immersion for the target open. -/
theorem moduleDerivedProperRefinementComparison_isIso_of_closedComplement
    {Z : Scheme.{u}} (i : Z ⟶ Y₂) [IsClosedImmersion i]
    (hcomp : Set.range j₂ = (Set.range i)ᶜ)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K) := by
  let := HasDerivedCategory.standard (ModuleSheaf Z Λ)
  have hLE := refinementPullback_torsion j₁ j₂ h sq Λ K hK
  have hopen := refinementUnit_open_isIso j₁ j₂ h sq Λ K hLE
  have hclosed := refinementUnit_closed_isIso j₂ h Λ i hcomp K hLE
  let : IsIso ((moduleDerivedAdjunction Λ h).unit.app
      ((moduleDerivedLowerShriek j₂ Λ).obj K)) :=
    moduleDerived_isIso_of_open_closed j₂ Λ i hcomp
      ((moduleDerivedAdjunction Λ h).unit.app ((moduleDerivedLowerShriek j₂ Λ).obj K))
  rw [moduleDerivedProperRefinementComparison_app]
  infer_instance

/-- Proper refinement preserves the original open extension by the original
unit comparison, for every bounded-below object with internal torsion homology. -/
theorem moduleDerivedProperRefinementComparison_isIso
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedProperRefinementComparison j₁ j₂ h sq Λ).app K) := by
  let I := IdealSheafData.vanishingIdeal j₂.opensRange.compl
  apply moduleDerivedProperRefinementComparison_isIso_of_closedComplement j₁ j₂ h sq Λ I.subschemeι
    (K := K) (hK := hK)
  have hI : Set.range I.subschemeι = (Set.range j₂)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  exact ((congrArg (fun T : Set Y₂ => Tᶜ) hI).trans
    (compl_compl (Set.range j₂))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
