/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.TwoGonNormalDegree

/-!
# Actual smooth rational components and their intrinsic degrees

Source: frozen R5 `LocalModels/Incidence/TwoGon.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom
open Scheme.Hom.Cartier
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- The actual left component is the literal projective line over the original
residue field, with the structural triangle retained in the isomorphism. -/
def leftComponentP1OverIso (e : TwoGonIso π) :
    Over.mk (leftComponentStructure π e) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)) :=
  Over.isoMk
    (leftComponentLineIso π e ≪≫ Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _)
    (by simp only [Iso.trans_hom, Over.mk_hom, Category.assoc,
      Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, leftComponentLineIso_over])

/-- The corresponding residue-field projective-line isomorphism for the
actual right component. -/
def rightComponentP1OverIso (e : TwoGonIso π) :
    Over.mk (rightComponentStructure π e) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)) :=
  Over.isoMk
    (rightComponentLineIso π e ≪≫ Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _)
    (by simp only [Iso.trans_hom, Over.mk_hom, Category.assoc,
      Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, rightComponentLineIso_over])

/-- Actual smooth rational closed-component geometry, including the exact
image subset of the actual special fibre and rationality over its original
residue field. -/
def actualSmoothRationalComponent (v : Set (obj π)) : Prop :=
  ∃ (C : Scheme.{u}) (i : C ⟶ (obj π)),
    IsClosedImmersion i ∧ Set.range i = v ∧ SmoothOfRelativeDimension 1 (i ≫ (structureMap π)) ∧
    Nonempty (Over.mk (i ≫ (structureMap π)) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)))

/-- Every actual two-gon component is smooth and genuinely isomorphic to the
literal projective line over the residue field, through its actual closed-image
presentation. -/
theorem actualComponent_smoothRational (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : actualSmoothRationalComponent π v.val := by
  classical
  by_cases h : v.val = twoGonLeftComponent π e
  · exact ⟨twoGonLeftComponentScheme π e, (twoGonLeftComponentMap π e).imageι,
      inferInstance, (twoGonLeftComponentScheme_range π e).trans h.symm,
      inferInstance, ⟨leftComponentP1OverIso π e⟩⟩
  · have hv := (Set.ext_iff.mp (twoGon_components_eq π e) v.val).mp v.property
    have h' := Set.mem_singleton_iff.mp ((Set.mem_insert_iff.mp hv).resolve_left h)
    exact ⟨twoGonRightComponentScheme π e, (twoGonRightComponentMap π e).imageι,
      inferInstance, (twoGonRightComponentScheme_range π e).trans h'.symm,
      inferInstance, ⟨rightComponentP1OverIso π e⟩⟩

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
variable (hcartier : RegularCodimOneIdealInvertible.{u})
  (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
  (havoid : IntegralAvoidanceCartierPullback.{u})
  (hunion : CartierSumIdealEqualsUnion.{u})
  (htensor : CartierIdealTensorProduct.{u})
  (hprincipal : FlatDVRFibreIdealTrivial.{u})
  (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
  (hprod : Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u})

/-- The actual left normal-bundle degree with all geometric degree hypotheses
proved from the actual polynomial-chart geometry. -/
def leftActualSelfIntersection (e : TwoGonIso π) : ℤ :=
  actualSelfIntersection (leftSurfaceMap π e) (leftComponentStructure π e)
    (leftComponent_dimension π e).le (leftComponent_productFormula π hprod e)
    (leftComponentIdealLineBundle π hcartier hregular e).property

/-- The actual right normal-bundle degree with all geometric degree hypotheses
proved from the actual polynomial-chart geometry. -/
def rightActualSelfIntersection (e : TwoGonIso π) : ℤ :=
  actualSelfIntersection (rightSurfaceMap π e) (rightComponentStructure π e)
    (rightComponent_dimension π e).le (rightComponent_productFormula π hprod e)
    (rightComponentIdealLineBundle π hcartier hregular e).property

include hcartier hregular havoid hunion htensor hprincipal hdegree hprod

theorem leftActualSelfIntersection_eq_neg_two (e : TwoGonIso π) :
    leftActualSelfIntersection π hcartier hregular hprod e = -2 :=
  leftComponent_selfIntersection π hcartier hregular havoid hunion htensor hprincipal hdegree e
    (leftComponent_dimension π e).le (leftComponent_productFormula π hprod e)

theorem rightActualSelfIntersection_eq_neg_two (e : TwoGonIso π) :
    rightActualSelfIntersection π hcartier hregular hprod e = -2 :=
  rightComponent_selfIntersection π hcartier hregular havoid hunion htensor hprincipal hdegree e
    (rightComponent_dimension π e).le (rightComponent_productFormula π hprod e)

/-- A degree attached to an actual irreducible component by the same selection
used by its exhaustive closed-component presentation. Values are actual normal
bundle degrees, never assigned integers. -/
def actualComponentSelfIntersection (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : ℤ :=
  if v.val = twoGonLeftComponent π e then leftActualSelfIntersection π hcartier hregular hprod e
  else rightActualSelfIntersection π hcartier hregular hprod e

theorem actualComponentSelfIntersection_eq_neg_two (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) :
    actualComponentSelfIntersection π hcartier hregular hprod e v = -2 := by
  unfold actualComponentSelfIntersection
  split_ifs
  · exact leftActualSelfIntersection_eq_neg_two π hcartier hregular havoid hunion htensor
      hprincipal hdegree hprod e
  · exact rightActualSelfIntersection_eq_neg_two π hcartier hregular havoid hunion htensor
      hprincipal hdegree hprod e

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
