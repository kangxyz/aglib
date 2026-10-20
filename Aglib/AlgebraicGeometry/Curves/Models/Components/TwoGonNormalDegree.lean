/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.TwoGonCartier
public import Aglib.AlgebraicGeometry.Curves.Models.Components.NormalDegree
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry

/-!
# The intrinsic minus-two degree of the literal two-gon components

Source: frozen R5 `LocalModels/Incidence/Cartier.lean`, revision
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
open Scheme.Hom Scheme.Hom.Cartier
open Scheme.Modules.Invertible Scheme.PinchedLine
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- The left closed component identified with its glued projective-line parametrization. -/
def leftComponentLineIso (e : TwoGonIso π) :
    twoGonLeftComponentScheme π e ≅ Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) :=
  (asIso (twoGonLeftComponentMap π e).toImage).symm

/-- The right closed component identified with its glued projective-line parametrization. -/
def rightComponentLineIso (e : TwoGonIso π) :
    twoGonRightComponentScheme π e ≅ Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) :=
  (asIso (twoGonRightComponentMap π e).toImage).symm

@[reassoc] theorem leftComponentLineIso_over (e : TwoGonIso π) :
    (leftComponentLineIso π e).hom ≫ Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) =
      leftComponentStructure π e := by
  apply (cancel_epi (twoGonLeftComponentMap π e).toImage).mp
  simp only [leftComponentLineIso, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  exact (twoGonLeftComponentMap_over π e).symm.trans
    (by simp only [leftComponentStructure, ← Category.assoc, Scheme.Hom.toImage_imageι])

@[reassoc] theorem rightComponentLineIso_over (e : TwoGonIso π) :
    (rightComponentLineIso π e).hom ≫ Scheme.PinchedLine.lineStructure
      (IsLocalRing.ResidueField R) =
      rightComponentStructure π e := by
  apply (cancel_epi (twoGonRightComponentMap π e).toImage).mp
  simp only [rightComponentLineIso, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  exact (twoGonRightComponentMap_over π e).symm.trans
    (by simp only [rightComponentStructure, ← Category.assoc, Scheme.Hom.toImage_imageι])

/-- The left component is proper over the residue field. -/
instance leftComponentStructure_proper (e : TwoGonIso π) : IsProper (leftComponentStructure π
  e) := by
  rw [← leftComponentLineIso_over]
  infer_instance

/-- The right component is proper over the residue field. -/
instance rightComponentStructure_proper (e : TwoGonIso π) : IsProper (rightComponentStructure π
  e) := by
  rw [← rightComponentLineIso_over]
  infer_instance

/-- The left component is locally of finite type over the residue field. -/
instance leftComponentStructure_finiteType (e : TwoGonIso π) :
    LocallyOfFiniteType (leftComponentStructure π e) := by
  rw [← leftComponentLineIso_over]
  infer_instance

/-- The right component is locally of finite type over the residue field. -/
instance rightComponentStructure_finiteType (e : TwoGonIso π) :
    LocallyOfFiniteType (rightComponentStructure π e) := by
  rw [← rightComponentLineIso_over]
  infer_instance

/-- The left component is smooth of relative dimension one over the residue field. -/
instance leftComponentStructure_smoothOne (e : TwoGonIso π) :
    SmoothOfRelativeDimension 1 (leftComponentStructure π e) := by
  rw [← leftComponentLineIso_over]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The right component is smooth of relative dimension one over the residue field. -/
instance rightComponentStructure_smoothOne (e : TwoGonIso π) :
    SmoothOfRelativeDimension 1 (rightComponentStructure π e) := by
  rw [← rightComponentLineIso_over]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The left closed component is a Noetherian scheme. -/
instance leftComponent_noetherian (e : TwoGonIso π) :
    AlgebraicGeometry.IsNoetherian (twoGonLeftComponentScheme π e) := by
  let : IsLocallyNoetherian (twoGonLeftComponentScheme π e) :=
    LocallyOfFiniteType.isLocallyNoetherian (leftComponentStructure π e)
  let : CompactSpace (twoGonLeftComponentScheme π e) :=
    QuasiCompact.compactSpace_of_compactSpace (leftComponentStructure π e)
  exact ⟨⟩

/-- The right closed component is a Noetherian scheme. -/
instance rightComponent_noetherian (e : TwoGonIso π) :
    AlgebraicGeometry.IsNoetherian (twoGonRightComponentScheme π e) := by
  let : IsLocallyNoetherian (twoGonRightComponentScheme π e) :=
    LocallyOfFiniteType.isLocallyNoetherian (rightComponentStructure π e)
  let : CompactSpace (twoGonRightComponentScheme π e) :=
    QuasiCompact.compactSpace_of_compactSpace (rightComponentStructure π e)
  exact ⟨⟩

/-- The stalk at a closed point of the left component is a discrete valuation ring. -/
instance leftComponent_closedStalk_dvr (e : TwoGonIso π)
    (d : Scheme.ClosedPoint (twoGonLeftComponentScheme π e)) :
    IsDiscreteValuationRing ((twoGonLeftComponentScheme π e).presheaf.stalk d.val) :=
  closedStalk_dvr_of_isoLine (leftComponentLineIso π e) d.val d.property

/-- The stalk at a closed point of the right component is a discrete valuation ring. -/
instance rightComponent_closedStalk_dvr (e : TwoGonIso π)
    (d : Scheme.ClosedPoint (twoGonRightComponentScheme π e)) :
    IsDiscreteValuationRing ((twoGonRightComponentScheme π e).presheaf.stalk d.val) :=
  closedStalk_dvr_of_isoLine (rightComponentLineIso π e) d.val d.property

theorem leftComponent_dimension (e : TwoGonIso π) :
    topologicalKrullDim (twoGonLeftComponentScheme π e) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ (leftComponentLineIso π
    e).hom.homeomorph.isHomeomorph).trans
    (line_dimension_eq_one _)

theorem rightComponent_dimension (e : TwoGonIso π) :
    topologicalKrullDim (twoGonRightComponentScheme π e) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ (rightComponentLineIso π
    e).hom.homeomorph.isHomeomorph).trans
    (line_dimension_eq_one _)

/-- The existing universal proper-curve product formula is applied to the
actual component, after its geometric hypotheses have all been proved. -/
theorem leftComponent_productFormula (hprod :
  Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u})
    (e : TwoGonIso π) : Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula
      (twoGonLeftComponentScheme π e) (leftComponentStructure π e) :=
  hprod _ _ _ (leftComponent_dimension π e)

theorem rightComponent_productFormula (hprod :
  Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u})
    (e : TwoGonIso π) : Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula
      (twoGonRightComponentScheme π e) (rightComponentStructure π e) :=
  hprod _ _ _ (rightComponent_dimension π e)

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
section Cartier
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
variable (hcartier : RegularCodimOneIdealInvertible.{u})
  (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
  (havoid : IntegralAvoidanceCartierPullback.{u})
  (hunion : CartierSumIdealEqualsUnion.{u})
  (htensor : CartierIdealTensorProduct.{u})
  (hprincipal : FlatDVRFibreIdealTrivial.{u})
  (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
include hcartier hregular havoid hunion htensor hprincipal hdegree

/-- Right component self-intersection is derived from its genuine Cartier
normal bundle, the principal reduced fibre, and the degree-two intersection. -/
theorem rightComponent_selfIntersection (e : TwoGonIso π)
    [AlgebraicGeometry.IsNoetherian (twoGonRightComponentScheme π e)]
    [∀ d : Scheme.ClosedPoint (twoGonRightComponentScheme π e),
      IsDiscreteValuationRing ((twoGonRightComponentScheme π e).presheaf.stalk d.val)]
    [IsProper (rightComponentStructure π e)]
    (hdim : topologicalKrullDim (twoGonRightComponentScheme π e) ≤ 1)
    (hprod : Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula
      (twoGonRightComponentScheme π e)
      (rightComponentStructure π e)) :
    actualSelfIntersection (rightSurfaceMap π e) (rightComponentStructure π e) hdim hprod
      (rightComponentIdealLineBundle π hcartier hregular e).property = -2 := by
  rw [selfIntersection_eq_negative_intersectionDegree havoid hdegree (leftSurfaceMap π e)
    (rightSurfaceMap π e) (rightComponentStructure π e) hdim hprod
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (rightComponentIdealLineBundle π hcartier hregular e).property
    (rightSurface_not_subset_left π e)
    (componentIdealClasses_sum_zero π hcartier hregular havoid hunion htensor hprincipal e),
    rightIntersection_degree]
  norm_num

/-- Left component uses the same actual product and the swapped actual
intersection; the two nodes remain distinct scheme-theoretically. -/
theorem leftComponent_selfIntersection (e : TwoGonIso π)
    [AlgebraicGeometry.IsNoetherian (twoGonLeftComponentScheme π e)]
    [∀ d : Scheme.ClosedPoint (twoGonLeftComponentScheme π e),
      IsDiscreteValuationRing ((twoGonLeftComponentScheme π e).presheaf.stalk d.val)]
    [IsProper (leftComponentStructure π e)]
    (hdim : topologicalKrullDim (twoGonLeftComponentScheme π e) ≤ 1)
    (hprod : Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula
      (twoGonLeftComponentScheme π e)
      (leftComponentStructure π e)) :
    actualSelfIntersection (leftSurfaceMap π e) (leftComponentStructure π e) hdim hprod
      (leftComponentIdealLineBundle π hcartier hregular e).property = -2 := by
  have hs : classOf Y (rightComponentIdealLineBundle π hcartier hregular e) +
      classOf Y (leftComponentIdealLineBundle π hcartier hregular e) = 0 := by
    rw [add_comm]
    exact componentIdealClasses_sum_zero π hcartier hregular havoid hunion htensor hprincipal e
  rw [selfIntersection_eq_negative_intersectionDegree havoid hdegree (rightSurfaceMap π e)
    (leftSurfaceMap π e) (leftComponentStructure π e) hdim hprod
    (rightComponentIdealLineBundle π hcartier hregular e).property
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (leftSurface_not_subset_right π e) hs, leftIntersection_degree]
  norm_num

end Cartier
end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
