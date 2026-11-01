/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenFullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.DerivedDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.DerivedOpenClosed
public import Aglib.CategoryTheory.Adjunction.UnitRestriction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CartesianExchangeComparison
public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Proper images of open extensions

The original proper exchange and original open-extension unit identify the
open restriction of a proper image of an open extension. Its adjoint under
open extension gives the canonical proper/open comparison. Proper base change
on the complementary closed subscheme proves that this comparison is invertible.
All constructions use the native torsion full subcategory and original maps.
Identification with other mixed-mate presentations and pasting are separate
coherence statements, not inferred merely from invertibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

private theorem isZero_of_invertible {D : Type*} [Category D] {X Y : D}
    (b : X ⟶ Y) (hb : IsIso b) (hY : IsZero Y) : IsZero X :=
  IsZero.of_iso hY (@asIso _ _ _ _ b hb)

universe u wX wY wU wV wZ wP

variable (Λ : Type (u + 1)) [Ring Λ]

private theorem openCounit_isIso_of_closed_zero
    {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    (B : DerivedCategory.Plus (ModuleSheaf Y Λ))
    (hB : IsZero ((moduleDerivedInverseImage Λ i).obj B)) :
    IsIso ((moduleDerivedLowerShriekAdjunction j Λ).counit.app B) := by
  let adj := moduleDerivedLowerShriekAdjunction j Λ
  have hopen : IsIso ((moduleDerivedInverseImage Λ j).map (adj.counit.app B)) :=
    inferInstance
  have hz := isZero_moduleDerivedInverseImage_lowerShriek j Λ i hcomp
    ((moduleDerivedInverseImage Λ j).obj B)
  have hclosed : IsIso ((moduleDerivedInverseImage Λ i).map (adj.counit.app B)) :=
    hz.isIso hB _
  exact moduleDerived_isIso_of_open_closed j Λ i hcomp (adj.counit.app B)

variable {V U X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
  (p' : V ⟶ U) (j : U ⟶ Y) (j' : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : IsPullback j' p' p j)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]

/-- The original proper image of the original open extension, on torsion input. -/
def moduleProperOpenImage :
    (moduleTorsionCohomologyPlus V Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf Y Λ) :=
  (moduleTorsionCohomologyPlus V Λ).ι ⋙ moduleDerivedLowerShriek j' Λ ⋙
    moduleDerivedDirectImage Λ p

/-- The original proper image on the open base, on the same torsion source. -/
def moduleOpenProperImage :
    (moduleTorsionCohomologyPlus V Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf U Λ) :=
  (moduleTorsionCohomologyPlus V Λ).ι ⋙ moduleDerivedDirectImage Λ p'

/-- Restriction comparison, defined by the original proper exchange and original
open-extension unit, not by choosing an isomorphism between the objects. -/
def moduleProperOpenRestriction :
    moduleProperOpenImage Λ p j' ⋙ moduleDerivedInverseImage Λ j ⟶
      moduleOpenProperImage Λ p' :=
  Functor.restrictionOfUnit (moduleTorsionCohomologyPlus V Λ).ι
    (moduleDerivedLowerShriek j' Λ) (moduleDerivedInverseImage Λ j')
    (moduleDerivedDirectImage Λ p) (moduleDerivedInverseImage Λ j)
    (moduleDerivedDirectImage Λ p')
    (moduleDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    (asIso (moduleDerivedLowerShriekAdjunction j' Λ).unit)

omit [IsProper p] in
private theorem originalOpenExchange_isIso :
    IsIso (moduleDerivedBaseChangeMap Λ p p' j j' sq.w.symm) := by
  rw [← moduleDerivedCartesianExchangeIso_hom p' j' j p sq.flip Λ]
  infer_instance

omit [IsProper p] in
/-- The original restriction comparison is invertible on the declared torsion source. -/
instance moduleProperOpenRestriction_isIso :
    IsIso (moduleProperOpenRestriction Λ p p' j j' sq) := by
  let := originalOpenExchange_isIso Λ p p' j j' sq
  exact Functor.restrictionOfUnit_isIso_of_isIso (moduleTorsionCohomologyPlus V Λ).ι
    (moduleDerivedLowerShriek j' Λ) (moduleDerivedInverseImage Λ j')
    (moduleDerivedDirectImage Λ p) (moduleDerivedInverseImage Λ j)
    (moduleDerivedDirectImage Λ p')
    (moduleDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    (asIso (moduleDerivedLowerShriekAdjunction j' Λ).unit)

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem extension_closedBaseChange_isIso
    {Z W : Scheme.{u}} (i : Z ⟶ Y) (q : W ⟶ X) (r : W ⟶ Z)
    (sqc : IsPullback q r p i)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wP} (ModuleSheaf W Λ)]
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    IsIso ((moduleDerivedBaseChangeMap Λ p r i q sqc.w.symm).app
      ((moduleDerivedLowerShriek j' Λ).obj K.obj)) := by
  exact Proper.properModuleDerivedBaseChange_isIso_of_torsion_homology
    Λ p r i q sqc ((moduleDerivedLowerShriek j' Λ).obj K.obj)
    (moduleDerivedLowerShriek_preservesTorsionCohomology j' Λ K.property)

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem extension_closedImage_isZero
    {Z W : Scheme.{u}} (i : Z ⟶ Y) (q : W ⟶ X) [IsClosedImmersion q]
    (r : W ⟶ Z) (sqc : IsPullback q r p i)
    (hq : Set.range j' = (Set.range q)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wP} (ModuleSheaf W Λ)]
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    IsZero ((moduleDerivedInverseImage Λ i).obj
      ((moduleProperOpenImage Λ p j').obj K)) := by
  have hz := isZero_moduleDerivedInverseImage_lowerShriek j' Λ q hq K.obj
  exact isZero_of_invertible
    ((moduleDerivedBaseChangeMap Λ p r i q sqc.w.symm).app
      ((moduleDerivedLowerShriek j' Λ).obj K.obj))
    (extension_closedBaseChange_isIso Λ p j' i q r sqc K)
    ((moduleDerivedDirectImage Λ r).map_isZero hz)

include sq

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem properOpenImage_closed_isZero
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    IsZero ((moduleDerivedInverseImage Λ i).obj
      ((moduleProperOpenImage Λ p j').obj K)) := by
  let := HasDerivedCategory.standard (ModuleSheaf (pullback p i) Λ)
  have hq : Set.range j' = (Set.range (pullback.fst p i))ᶜ := by
    rw [Scheme.Pullback.Fibre.pullback_range_fst sq, hcomp, Set.preimage_compl]
    exact congrArg (fun T : Set X => Tᶜ) (Scheme.Pullback.range_fst p i).symm
  exact extension_closedImage_isZero Λ p j' i (pullback.fst p i) (pullback.snd p i)
    (IsPullback.of_hasPullback p i) hq K

private theorem properOpenImage_counit_isIso
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    IsIso ((moduleDerivedLowerShriekAdjunction j Λ).counit.app
      ((moduleProperOpenImage Λ p j').obj K)) := by
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  let := HasDerivedCategory.standard (ModuleSheaf I.subscheme Λ)
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hcomp : Set.range j = (Set.range I.subschemeι)ᶜ :=
    ((congrArg (fun T : Set Y => Tᶜ) hI).trans (compl_compl (Set.range j))).symm
  exact openCounit_isIso_of_closed_zero Λ j I.subschemeι hcomp _
    (properOpenImage_closed_isZero Λ p p' j j' sq I.subschemeι hcomp K)

/-- The original adjoint transpose of inverse proper exchange on the open part.
Its definition retains the original lower-shriek counit and proper exchange. -/
def moduleProperOpenComparison :
    moduleOpenProperImage Λ p' ⋙ moduleDerivedLowerShriek j Λ ⟶
      moduleProperOpenImage Λ p j' :=
  Functor.whiskerRight (asIso (moduleProperOpenRestriction Λ p p' j j' sq)).inv
      (moduleDerivedLowerShriek j Λ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (moduleProperOpenImage Λ p j')
      (moduleDerivedLowerShriekAdjunction j Λ).counit ≫
    (Functor.rightUnitor _).hom

omit [IsProper p] in
/-- Components are the original counit after the inverse restriction comparison. -/
theorem moduleProperOpenComparison_app
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    (moduleProperOpenComparison Λ p p' j j' sq).app K =
      (moduleDerivedLowerShriek j Λ).map
        ((asIso (moduleProperOpenRestriction Λ p p' j j' sq)).inv.app K) ≫
      (moduleDerivedLowerShriekAdjunction j Λ).counit.app
        ((moduleProperOpenImage Λ p j').obj K) := by
  simp [moduleProperOpenComparison]

omit [IsProper p] in
/-- The comparison is characterized by its original open adjunction and
inverse restriction exchange. -/
theorem moduleProperOpenComparison_homEquiv
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    (moduleDerivedLowerShriekAdjunction j Λ).homEquiv _ _
      ((moduleProperOpenComparison Λ p p' j j' sq).app K) =
      (asIso (moduleProperOpenRestriction Λ p p' j j' sq)).inv.app K := by
  apply ((moduleDerivedLowerShriekAdjunction j Λ).homEquiv _ _).eq_symm_apply.mp
  rw [moduleProperOpenComparison_app]
  exact ((moduleDerivedLowerShriekAdjunction j Λ).homEquiv_counit _ _ _).symm

/-- Proper image commutes with open extension on the actual torsion D+ source. -/
instance moduleProperOpenComparison_isIso :
    IsIso (moduleProperOpenComparison Λ p p' j j' sq) := by
  have h (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
      IsIso ((moduleProperOpenComparison Λ p p' j j' sq).app K) := by
    rw [moduleProperOpenComparison_app]
    let := properOpenImage_counit_isIso Λ p p' j j' sq K
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Canonical proper/open interchange, with the unchanged original comparison map. -/
def moduleProperOpenComparisonIso :
    moduleOpenProperImage Λ p' ⋙ moduleDerivedLowerShriek j Λ ≅
      moduleProperOpenImage Λ p j' :=
  asIso (moduleProperOpenComparison Λ p p' j j' sq)

end AlgebraicGeometry.Scheme.EtaleCohomology
