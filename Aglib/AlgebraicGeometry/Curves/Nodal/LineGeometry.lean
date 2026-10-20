/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Native
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Actual line geometry used by component degree

Source: frozen R5 `Curves/ProjectiveLine/Geometry.lean:101–208` and
`LocalModels/Incidence/Cartier.lean:535–562`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
Only the polynomial-chart smoothness, actual closed-point local rings and
Krull dimensions are extracted. Both fixed homogeneous P¹ and the original
normalization gluing retain their proved comparison and structural maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial TopologicalSpace
open scoped Polynomial
open Polynomial.PinchedPair
open Scheme.OverField (FScheme)
universe u

namespace Polynomial
variable (k : Type u) [Field k]

/-- The one-variable polynomial algebra is standard smooth of relative dimension one over `k`. -/
instance isStandardSmoothOfRelativeDimension_one : Algebra.IsStandardSmoothOfRelativeDimension
  1 k k[X] := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{u+1} k) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k PUnit.{u+1}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv
    k PUnit.{u+1})

end Polynomial
namespace AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k]

/-- The affine polynomial line is smooth of relative dimension one over `k`. -/
instance affineLine_smoothOne : SmoothOfRelativeDimension 1 (Spec.algebraMap k k[X]) := by
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

/-- The infinity chart is smooth of relative dimension one over `k`. -/
instance infinity_smoothOne : SmoothOfRelativeDimension 1 (Spec.algebraMap k (infinityChartRing
  k)) := by
  rw [← Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom k k[X] (infinityChartRing k))]
  change SmoothOfRelativeDimension 1 (Scheme.PinchedLine.ProjectiveComparison.infinityInclusion
    k ≫ Spec.algebraMap k k[X])
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- Smooth relative dimension one is proved on the actual two affine charts. -/
instance line_smoothOne : SmoothOfRelativeDimension 1 (lineStructure k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (OpenNormalizationGluing.twoChartCover (normalizationOverlapInclusion k) (gluingToInfinity k))
  intro b
  cases b
  · change SmoothOfRelativeDimension 1
      (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ lineStructure k)
    simp only [lineStructure, pushout.inl_desc]
    infer_instance
  · change SmoothOfRelativeDimension 1
      (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) ≫ lineStructure k)
    simp only [lineStructure, pushout.inr_desc]
    infer_instance

/-- The glued projective line is a Noetherian scheme. -/
instance line_noetherian : AlgebraicGeometry.IsNoetherian (lineGluing k) := by
  let : IsLocallyNoetherian (lineGluing k) := LocallyOfFiniteType.isLocallyNoetherian
    (lineStructure k)
  let : CompactSpace (lineGluing k) := QuasiCompact.compactSpace_of_compactSpace (lineStructure k)
  exact ⟨⟩

/-- Actual field-line structure, retaining its specified structural map. -/
abbrev lineOver : FScheme k := Over.mk (lineStructure k)

/-- The normalization gluing identified with the native projective line as a scheme over `k`. -/
def lineIsoP1Over : lineOver k ≅ Scheme.OverField.Curve.ProjectiveLine.projectiveLineOver k :=
  Over.isoMk (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k)
    (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over k)

/-- A closed point of the actual affine polynomial line has a DVR stalk:
its maximal ideal is nonzero, and k[T] is Dedekind. -/
theorem affineLine_closedStalk_dvr (x : Spec (.of k[X]))
    (hx : IsClosed ({x} : Set (Spec (.of k[X])))) :
    IsDiscreteValuationRing ((Spec (.of k[X])).presheaf.stalk x) := by
  have hm : x.asIdeal.IsMaximal := PrimeSpectrum.isClosed_singleton_iff_isMaximal x |>.mp hx
  have hn : x.asIdeal ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (Polynomial.not_isField k)
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hn
    (Localization.AtPrime x.asIdeal)
  let e : Localization.AtPrime x.asIdeal ≃+* ((Spec (.of k[X])).presheaf.stalk x) :=
    (StructureSheaf.stalkIso k[X] x).toRingEquiv
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

end AlgebraicGeometry.Scheme.PinchedLine
namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable (k : Type u) [Field k]

/-- The native projective line is an integral scheme. -/
instance projectiveP1_integral : IsIntegral (Scheme.ProjectiveLine.projectiveP1 k) :=
  IsIntegral.of_isIso (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).hom

/-- Every closed point of literal Proj(k[X₀,X₁]) lies in an actual polynomial
chart, so its actual local ring is a DVR without a smooth-regularity premise. -/
theorem closedStalk_dvr (x : Scheme.ProjectiveLine.projectiveP1 k)
    (hx : IsClosed ({x} : Set (Scheme.ProjectiveLine.projectiveP1 k))) :
    IsDiscreteValuationRing ((Scheme.ProjectiveLine.projectiveP1 k).presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := Scheme.ProjectiveLine.chart_covered k x
  have hy : IsClosed ({y} : Set (Spec (.of k[X]))) := by
    convert hx.preimage (Scheme.ProjectiveLine.chart k i).continuous using 1
    ext z
    exact (Scheme.ProjectiveLine.chart k i).isOpenEmbedding.injective.eq_iff.symm
  let := Scheme.PinchedLine.affineLine_closedStalk_dvr k y hy
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso ((Scheme.ProjectiveLine.chart k i).stalkMap y)).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.ProjectiveLine
namespace AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k]

/-- Transport of actual closed-point DVRs through the proved line/Proj iso. -/
theorem line_closedStalk_dvr (x : lineGluing k)
    (hx : IsClosed ({x} : Set (lineGluing k))) :
    IsDiscreteValuationRing ((lineGluing k).presheaf.stalk x) := by
  let e := Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k
  have hy : IsClosed ({e.hom x} : Set (Scheme.ProjectiveLine.projectiveP1 k)) := by
    convert e.hom.homeomorph.isClosedMap _ hx using 1
    exact Set.image_singleton.symm
  let := Scheme.ProjectiveLine.closedStalk_dvr k (e.hom x) hy
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- Dimension at every actual closed point is one, by the proved DVR stalk. -/
theorem line_closedStalk_dimension (x : lineGluing k)
    (hx : IsClosed ({x} : Set (lineGluing k))) :
    ringKrullDim ((lineGluing k).presheaf.stalk x) = 1 := by
  let := line_closedStalk_dvr k x hx
  exact IsDiscreteValuationRing.ringKrullDim_eq_one _

/-- The global dimension upper bound required by the existing Picard degree
API. Specialization to closed points works over every field, with no algebraic
closedness or independent smooth-dimension premise. -/
theorem line_dimension_le_one : topologicalKrullDim (lineGluing k) ≤ 1 := by
  let : JacobsonSpace (lineGluing k) := LocallyOfFiniteType.jacobsonSpace (lineStructure k)
  change Order.krullDim (IrreducibleCloseds (lineGluing k)) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := lineGluing k)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set (lineGluing k)))
    (Set.Nonempty.closure (Set.singleton_nonempty x)) isClosed_closure.isLocallyClosed
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  have hyheight : (Order.coheight y : WithBot ℕ∞) = 1 := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact line_closedStalk_dimension k y hyclosed
  exact (WithBot.coe_le_coe.mpr (Order.coheight_anti hyx)).trans hyheight.le

/-- Actual integral-curve DVR stalks transport through actual scheme isos. -/
theorem closedStalk_dvr_of_isoLine {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (e : C ≅ Scheme.PinchedLine.lineGluing k) (c : C) (hc : IsClosed ({c} : Set C)) :
    IsDiscreteValuationRing (C.presheaf.stalk c) := by
  have hec : IsClosed ({e.hom c} : Set (Scheme.PinchedLine.lineGluing k)) := by
    convert e.hom.homeomorph.isClosedMap _ hc using 1
    exact Set.image_singleton.symm
  let := line_closedStalk_dvr k (e.hom c) hec
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (e.hom.stalkMap c)).commRingCatIsoToRingEquiv

/-- The line is not zero-dimensional: a closed point has the proved DVR
local ring. No independent smooth-dimension premise is used. -/
theorem line_dimension_eq_one (k : Type u) [Field k] :
    topologicalKrullDim (Scheme.PinchedLine.lineGluing k) = 1 := by
  refine le_antisymm (line_dimension_le_one k) ?_
  let : JacobsonSpace (Scheme.PinchedLine.lineGluing k) :=
    LocallyOfFiniteType.jacobsonSpace (Scheme.PinchedLine.lineStructure k)
  obtain ⟨y, _, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set (Scheme.PinchedLine.lineGluing k)))
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  change 1 ≤ Order.krullDim (IrreducibleCloseds (Scheme.PinchedLine.lineGluing k))
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α :=
    Scheme.PinchedLine.lineGluing k))]
  have hy : (Order.coheight y : WithBot ℕ∞) = 1 := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact line_closedStalk_dimension k y hyclosed
  rw [← hy]
  exact Order.coheight_le_krullDim y

end AlgebraicGeometry.Scheme.PinchedLine
