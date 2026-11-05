/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Pullback.SectionPointLiftImmersion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.WholeSectionResidueMarks

/-! # Original whole-section residue marks on an affine target chart

The canonical finite Henselian model belongs to the restriction of the
original finite source to the chosen affine target chart. Its residue points
still lie on the original section on underlying points. Reduced immersion
factorization gives the exact section equation, so the unchanged global lift
supplies actual marks on the restricted cover. The global section need not
factor through the affine chart, and separatedness is not required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X S V G : Scheme.{u}} (p : X ⟶ S) (r : V ⟶ S) [IsFinite r]
    (e : Spec (.of R) ⟶ X)

local notation "f" => pullback.fst p r
local notation "fO" => pullback.snd f e
local notation "qO" => pullback.fst f e

/-- The original X-coordinate of every canonical restricted-source residue
point lies in the original section's image from the single target-point condition. -/
theorem affineChartLimitResidueMap_section_support
    (σ : S ⟶ X)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    Set.range ((limitResidueMap R Ω fO i ≫ qO) ≫ f) ⊆ Set.range σ := by
  let z := limitResidueMap R Ω fO i
  have hproj : (z ≫ qO) ≫ f = (z ≫ fO) ≫ e :=
    (Category.assoc z qO f).trans
      ((congrArg (fun a : pullback f e ⟶ X => z ≫ a)
        (pullback.condition («f» := f) (g := e))).trans (Category.assoc z fO e).symm)
  rintro _ ⟨t, rfl⟩
  obtain rfl : t = IsLocalRing.closedPoint
      (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) := Subsingleton.elim _ _
  have heval : ((z ≫ qO) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
      (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) :=
    (congrArg (fun a :
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ X =>
        a (IsLocalRing.closedPoint
          (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)))) hproj).trans
      (congrArg e (limitResidueMap_basepoint R Ω fO i))
  exact heval.symm ▸ hpoint

/-- The unchanged source-base coordinate of the actual finite-model residue point. -/
def affineChartWholeSectionBasePoint
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ V :=
  (limitResidueMap R Ω fO i ≫ qO) ≫ pullback.snd p r

/-- The base point followed by the original global section lift lies over
the original residue map before target restriction. This is the mark used by
induction on the whole original source curve. -/
@[reassoc]
theorem affineChartWholeSectionBasePoint_lift_over
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    (affineChartWholeSectionBasePoint R Ω p r e i ≫ ρ) ≫ g =
      limitResidueMap R Ω fO i ≫ qO := by
  have h := pullback.sectionLiftPoint_over p r σ hσ g ρ hρ _
    (pullback_section_condition_of_reduced_range_subset p r σ hσ _
      (affineChartLimitResidueMap_section_support R Ω p r e σ hpoint i))
  simpa only [affineChartWholeSectionBasePoint, pullback.sectionLiftPoint, Category.assoc] using h

/-- The original whole lifted section gives the actual point of the cover
restricted to the affine target chart, over the unchanged canonical residue map. -/
def affineChartWholeSectionResidueMark
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
      pullback g qO :=
  pullback.lift
    (pullback.sectionLiftPoint p r ρ (limitResidueMap R Ω fO i ≫ qO))
    (limitResidueMap R Ω fO i)
    (pullback.sectionLiftPoint_over p r σ hσ g ρ hρ _
      (pullback_section_condition_of_reduced_range_subset p r σ hσ _
        (affineChartLimitResidueMap_section_support R Ω p r e σ hpoint i)))

/-- The mark is over the exact original restricted finite-source residue map. -/
@[reassoc]
theorem affineChartWholeSectionResidueMark_over
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    affineChartWholeSectionResidueMark R Ω p r e σ hσ g ρ hρ hpoint i ≫
      pullback.snd g qO = limitResidueMap R Ω fO i :=
  pullback.lift_snd ..

/-- The original global lift and original source-field coordinate remain
literally the first projection of the restricted mark. -/
@[reassoc]
theorem affineChartWholeSectionResidueMark_original
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) :
    affineChartWholeSectionResidueMark R Ω p r e σ hσ g ρ hρ hpoint i ≫
      pullback.fst g qO =
        (limitResidueMap R Ω fO i ≫ qO) ≫ pullback.snd p r ≫ ρ :=
  pullback.lift_fst ..

/-- After induction on the whole original curve, restrict its actual pointed
etale chart. The original point, residue field and finite-source map are unchanged. -/
def affineChartWholeSectionEtaleMark
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) (U : G.Etale)
    (u : Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ U.left)
    (hu : u ≫ U.hom = affineChartWholeSectionBasePoint R Ω p r e i ≫ ρ) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
      pullback (U.hom ≫ g) qO :=
  pullback.lift u (limitResidueMap R Ω fO i)
    ((Category.assoc u U.hom g).symm.trans
      ((congrArg (fun a :
        Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ G => a ≫ g)
        hu).trans
          (affineChartWholeSectionBasePoint_lift_over R Ω p r e σ hσ g ρ hρ hpoint i)))

@[reassoc]
theorem affineChartWholeSectionEtaleMark_original
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) (U : G.Etale)
    (u : Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ U.left)
    (hu : u ≫ U.hom = affineChartWholeSectionBasePoint R Ω p r e i ≫ ρ) :
    affineChartWholeSectionEtaleMark R Ω p r e σ hσ g ρ hρ hpoint i U u hu ≫
      pullback.fst (U.hom ≫ g) qO = u :=
  pullback.lift_fst ..

/-- This is the literal mark equation required by finite pointed stage lifting
on the affine target, after the original whole-curve induction step. -/
@[reassoc]
theorem affineChartWholeSectionEtaleMark_over
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω fO)) (U : G.Etale)
    (u : Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ U.left)
    (hu : u ≫ U.hom = affineChartWholeSectionBasePoint R Ω p r e i ≫ ρ) :
    affineChartWholeSectionEtaleMark R Ω p r e σ hσ g ρ hρ hpoint i U u hu ≫
      pullback.snd (U.hom ≫ g) qO = limitResidueMap R Ω fO i :=
  pullback.lift_snd ..

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
