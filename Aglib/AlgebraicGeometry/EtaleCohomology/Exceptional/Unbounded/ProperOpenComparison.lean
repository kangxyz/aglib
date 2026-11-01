/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperBaseChangeTheorem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenClosedDetection
public import Aglib.CategoryTheory.Adjunction.UnitRestriction
public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Proper images of open extensions

The original proper exchange and original open-extension unit identify the
open restriction of a proper image of an open extension. Its adjoint under
open extension gives the canonical proper/open comparison. Proper base change
on the complementary closed subscheme proves that this comparison is invertible.
All constructions use the original maps on the full native unbounded categories.
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
    (B : DerivedCategory (ModuleSheaf Y Λ))
    (hB : IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj B)) :
    IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app B) := by
  let adj := moduleUnboundedDerivedLowerShriekAdjunction j Λ
  have hopen : IsIso ((moduleUnboundedDerivedInverseImage Λ j).map (adj.counit.app B)) :=
    inferInstance
  have hz := isZero_moduleUnboundedDerivedInverseImage_lowerShriek j Λ i hcomp
    ((moduleUnboundedDerivedInverseImage Λ j).obj B)
  have hclosed : IsIso ((moduleUnboundedDerivedInverseImage Λ i).map (adj.counit.app B)) :=
    hz.isIso hB _
  exact moduleUnboundedDerived_isIso_of_open_closed j Λ i hcomp (adj.counit.app B)

variable {V U X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
  (p' : V ⟶ U) (j : U ⟶ Y) (j' : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : IsPullback j' p' p j)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]

/-- The original proper image of the original open extension, on all unbounded input. -/
def moduleUnboundedProperOpenImage :
    DerivedCategory (ModuleSheaf V Λ) ⥤
      DerivedCategory (ModuleSheaf Y Λ) :=
  (𝟭 (DerivedCategory (ModuleSheaf V Λ))) ⋙ moduleUnboundedDerivedLowerShriek j' Λ ⋙
    moduleUnboundedDerivedDirectImage Λ p

/-- The original proper image on the open base, on the same unbounded source. -/
def moduleUnboundedOpenProperImage :
    DerivedCategory (ModuleSheaf V Λ) ⥤
      DerivedCategory (ModuleSheaf U Λ) :=
  (𝟭 (DerivedCategory (ModuleSheaf V Λ))) ⋙ moduleUnboundedDerivedDirectImage Λ p'

/-- Restriction comparison, defined by the original proper exchange and original
open-extension unit, not by choosing an isomorphism between the objects. -/
def moduleUnboundedProperOpenRestriction :
    moduleUnboundedProperOpenImage Λ p j' ⋙ moduleUnboundedDerivedInverseImage Λ j ⟶
      moduleUnboundedOpenProperImage Λ p' :=
  Functor.restrictionOfUnit (𝟭 (DerivedCategory (ModuleSheaf V Λ)))
    (moduleUnboundedDerivedLowerShriek j' Λ) (moduleUnboundedDerivedInverseImage Λ j')
    (moduleUnboundedDerivedDirectImage Λ p) (moduleUnboundedDerivedInverseImage Λ j)
    (moduleUnboundedDerivedDirectImage Λ p')
    (moduleUnboundedDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    (asIso (moduleUnboundedDerivedLowerShriekAdjunction j' Λ).unit)

omit [IsProper p] in
private theorem originalOpenExchange_isIso :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ p p' j j' sq.w.symm) := by
  exact moduleUnboundedDerivedBaseChange_isIso_of_etale p' j' j p sq.flip Λ

omit [IsProper p] in
/-- The original restriction comparison is invertible on every native unbounded input. -/
instance moduleUnboundedProperOpenRestriction_isIso :
    IsIso (moduleUnboundedProperOpenRestriction Λ p p' j j' sq) := by
  let := originalOpenExchange_isIso Λ p p' j j' sq
  exact Functor.restrictionOfUnit_isIso_of_isIso (𝟭 (DerivedCategory (ModuleSheaf V Λ)))
    (moduleUnboundedDerivedLowerShriek j' Λ) (moduleUnboundedDerivedInverseImage Λ j')
    (moduleUnboundedDerivedDirectImage Λ p) (moduleUnboundedDerivedInverseImage Λ j)
    (moduleUnboundedDerivedDirectImage Λ p')
    (moduleUnboundedDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    (asIso (moduleUnboundedDerivedLowerShriekAdjunction j' Λ).unit)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem extension_closedBaseChange_isIso
    {Z W : Scheme.{u}} (i : Z ⟶ Y) (q : W ⟶ X) (r : W ⟶ Z)
    (sqc : IsPullback q r p i)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wP} (ModuleSheaf W Λ)]
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    IsIso ((moduleUnboundedDerivedBaseChangeMap Λ p r i q sqc.w.symm).app
      ((moduleUnboundedDerivedLowerShriek j' Λ).obj K)) := by
  let := Proper.properModuleUnboundedDerivedBaseChange_isIso
    Λ p r i q sqc N hN hΛ
  infer_instance

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem extension_closedImage_isZero
    {Z W : Scheme.{u}} (i : Z ⟶ Y) (q : W ⟶ X) [IsClosedImmersion q]
    (r : W ⟶ Z) (sqc : IsPullback q r p i)
    (hq : Set.range j' = (Set.range q)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    [HasDerivedCategory.{wP} (ModuleSheaf W Λ)]
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj
      ((moduleUnboundedProperOpenImage Λ p j').obj K)) := by
  have hz := isZero_moduleUnboundedDerivedInverseImage_lowerShriek j' Λ q hq K
  exact isZero_of_invertible
    ((moduleUnboundedDerivedBaseChangeMap Λ p r i q sqc.w.symm).app
      ((moduleUnboundedDerivedLowerShriek j' Λ).obj K))
    (extension_closedBaseChange_isIso Λ p j' N hN hΛ i q r sqc K)
    ((moduleUnboundedDerivedDirectImage Λ r).map_isZero hz)

include sq

omit [IsOpenImmersion j] [HasDerivedCategory (ModuleSheaf U Λ)] in
private theorem properOpenImage_closed_isZero
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    IsZero ((moduleUnboundedDerivedInverseImage Λ i).obj
      ((moduleUnboundedProperOpenImage Λ p j').obj K)) := by
  let := HasDerivedCategory.standard (ModuleSheaf (pullback p i) Λ)
  have hq : Set.range j' = (Set.range (pullback.fst p i))ᶜ := by
    rw [Scheme.Pullback.Fibre.pullback_range_fst sq, hcomp, Set.preimage_compl]
    exact congrArg (fun T : Set X => Tᶜ) (Scheme.Pullback.range_fst p i).symm
  exact extension_closedImage_isZero Λ p j' N hN hΛ i (pullback.fst p i) (pullback.snd p i)
    (IsPullback.of_hasPullback p i) hq K

private theorem properOpenImage_counit_isIso
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    IsIso ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app
      ((moduleUnboundedProperOpenImage Λ p j').obj K)) := by
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  let := HasDerivedCategory.standard (ModuleSheaf I.subscheme Λ)
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hcomp : Set.range j = (Set.range I.subschemeι)ᶜ :=
    ((congrArg (fun T : Set Y => Tᶜ) hI).trans (compl_compl (Set.range j))).symm
  exact openCounit_isIso_of_closed_zero Λ j I.subschemeι hcomp _
    (properOpenImage_closed_isZero Λ p p' j j' sq N hN hΛ I.subschemeι hcomp K)

omit N hN hΛ in
/-- The original adjoint transpose of inverse proper exchange on the open part.
Its definition retains the original lower-shriek counit and proper exchange. -/
def moduleUnboundedProperOpenComparison :
    moduleUnboundedOpenProperImage Λ p' ⋙ moduleUnboundedDerivedLowerShriek j Λ ⟶
      moduleUnboundedProperOpenImage Λ p j' :=
  Functor.whiskerRight (asIso (moduleUnboundedProperOpenRestriction Λ p p' j j' sq)).inv
      (moduleUnboundedDerivedLowerShriek j Λ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (moduleUnboundedProperOpenImage Λ p j')
      (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit ≫
    (Functor.rightUnitor _).hom

omit N hN hΛ [IsProper p] in
/-- Components are the original counit after the inverse restriction comparison. -/
theorem moduleUnboundedProperOpenComparison_app
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    (moduleUnboundedProperOpenComparison Λ p p' j j' sq).app K =
      (moduleUnboundedDerivedLowerShriek j Λ).map
        ((asIso (moduleUnboundedProperOpenRestriction Λ p p' j j' sq)).inv.app K) ≫
      (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app
        ((moduleUnboundedProperOpenImage Λ p j').obj K) := by
  simp [moduleUnboundedProperOpenComparison]

omit N hN hΛ [IsProper p] in
/-- The comparison is characterized by its original open adjunction and
inverse restriction exchange. -/
theorem moduleUnboundedProperOpenComparison_homEquiv
    (K : DerivedCategory (ModuleSheaf V Λ)) :
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).homEquiv _ _
      ((moduleUnboundedProperOpenComparison Λ p p' j j' sq).app K) =
      (asIso (moduleUnboundedProperOpenRestriction Λ p p' j j' sq)).inv.app K := by
  apply ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).homEquiv _ _).eq_symm_apply.mp
  rw [moduleUnboundedProperOpenComparison_app]
  exact ((moduleUnboundedDerivedLowerShriekAdjunction j Λ).homEquiv_counit _ _ _).symm

/-- Proper image commutes with open extension on the unbounded source
over the stated torsion coefficient ring. -/
theorem moduleUnboundedProperOpenComparison_isIso :
    IsIso (moduleUnboundedProperOpenComparison Λ p p' j j' sq) := by
  have h (K : DerivedCategory (ModuleSheaf V Λ)) :
      IsIso ((moduleUnboundedProperOpenComparison Λ p p' j j' sq).app K) := by
    rw [moduleUnboundedProperOpenComparison_app]
    let := properOpenImage_counit_isIso Λ p p' j j' sq N hN hΛ K
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Canonical proper/open interchange, with the unchanged original comparison map. -/
def moduleUnboundedProperOpenComparisonIso :
    moduleUnboundedOpenProperImage Λ p' ⋙ moduleUnboundedDerivedLowerShriek j Λ ≅
      moduleUnboundedProperOpenImage Λ p j' :=
  let := moduleUnboundedProperOpenComparison_isIso Λ p p' j j' sq N hN hΛ
  asIso (moduleUnboundedProperOpenComparison Λ p p' j j' sq)

end AlgebraicGeometry.Scheme.EtaleCohomology
