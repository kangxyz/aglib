/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalNeighborhood.Basic
public import Aglib.AlgebraicGeometry.Curves.Nodal.SplitChart
public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.CoordinateTransport
public import Aglib.RingTheory.PlaneNode.Residue
public import Aglib.RingTheory.PlaneNode.CoordinateTransport
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Native extraction from the R5 local-model source
`PointedResolution.EtaleNode.CommonChart`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`fde7e4ab022c6077b626d4b418d07d7024d1d49239d091f10ab72a0cbec327ca`.
Source111–619: actual tangent coordinates, origin ideals, common chart, exact structural/residue
  maps and centre kernels. Generic field-valued residues reuse the incoming TangentNode API.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

universe u

noncomputable section
open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry
open WeierstrassCurve WeierstrassCurve.Affine.TangentNode
open AlgebraicGeometry.Scheme.WeierstrassNode
namespace WeierstrassCurve.Affine.TangentNode
variable {R : Type u} [CommRing R]

/-- The affine x-coordinate mapped into the localized tangent chart. -/
abbrev chartX (W : WeierstrassCurve R) : TangentChart W :=
  algebraMap (TangentRing W) (TangentChart W) (tangentX W)
/-- The affine y-coordinate mapped into the localized tangent chart. -/
abbrev chartY (W : WeierstrassCurve R) : TangentChart W :=
  algebraMap (TangentRing W) (TangentChart W) (tangentY W)
/-- The tangent-root coordinate mapped into the localized tangent chart. -/
abbrev chartT (W : WeierstrassCurve R) : TangentChart W :=
  algebraMap (TangentRing W) (TangentChart W) (tangentT W)

@[simp] theorem nodeChartMap_u (W : WeierstrassCurve R) (h3) (h4) :
    AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap W h3 h4 (PlaneNode.U W.a₆) = chartY W -
      chartT W * chartX W := by
  simp [AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap, nodeToTangent, chartY, chartT,
    chartX]

@[simp] theorem nodeChartMap_v (W : WeierstrassCurve R) (h3) (h4) :
    AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap W h3 h4 (PlaneNode.V W.a₆) =
      chartY W + (algebraMap R (TangentChart W) W.a₁ + chartT W) * chartX W := by
  simp [AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap, nodeToTangent, chartY, chartT,
    chartX,
    ← IsScalarTower.algebraMap_apply R (TangentRing W)]

theorem chart_tangentDifference_isUnit (W : WeierstrassCurve R) :
    IsUnit (2 * chartT W + algebraMap R (TangentChart W) W.a₁) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := TangentChart W) (tangentDenom W)
  simp only [tangentDenom_eq, map_mul] at h
  have h' := isUnit_of_mul_isUnit_left h
  simpa only [map_add, map_mul, map_ofNat,
    ← IsScalarTower.algebraMap_apply R (TangentRing W)] using h'

/-- The invertible tangent-difference coordinate change preserves the actual
origin ideal over every commutative coefficient ring. -/
private theorem factor_coordinate_ideal_eq (X Y T a : R) (hd : IsUnit (2 * T + a)) :
    Ideal.span {X, Y} = Ideal.span {Y - T * X, Y + (a + T) * X} := by
  let J : Ideal R := Ideal.span {Y - T * X, Y + (a + T) * X}
  have hu : Y - T * X ∈ J := Ideal.subset_span (by simp)
  have hv : Y + (a + T) * X ∈ J := Ideal.subset_span (by simp)
  have hx : X ∈ J := by
    apply (J.unit_mul_mem_iff_mem hd).mp
    have he : (2 * T + a) * X = (Y + (a + T) * X) - (Y - T * X) := by ring
    rw [he]
    exact J.sub_mem hv hu
  have hy : Y ∈ J := by
    have he : Y = (Y - T * X) + T * X := by ring
    rw [he]
    exact J.add_mem hu (J.mul_mem_left _ hx)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hx' : X ∈ Ideal.span ({X, Y} : Set R) := Ideal.subset_span (by simp)
    have hy' : Y ∈ Ideal.span ({X, Y} : Set R) := Ideal.subset_span (by simp)
    rcases hz with rfl | rfl
    · exact (Ideal.span {X, Y}).sub_mem hy' ((Ideal.span {X, Y}).mul_mem_left _ hx')
    · exact (Ideal.span {X, Y}).add_mem hy' ((Ideal.span {X, Y}).mul_mem_left _ hx')

theorem chart_origin_ideal_eq (W : WeierstrassCurve R) (h3) (h4) :
    Ideal.span {chartX W, chartY W} =
      Ideal.span {AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap W h3 h4 (PlaneNode.U
        W.a₆), AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap W h3 h4 (PlaneNode.V W.a₆)}
        := by
  rw [nodeChartMap_u, nodeChartMap_v]
  exact factor_coordinate_ideal_eq _ _ _ _ (chart_tangentDifference_isUnit W)

private theorem unit_scale_coordinate_ideal_eq (X Y : R) (a : Rˣ) :
    Ideal.span {X, Y} = Ideal.span {(a : R) * X, Y} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    all_goals rw [hz]
    · exact ((Ideal.span {(a : R) * X,Y}).unit_mul_mem_iff_mem a.isUnit).mp
        (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    all_goals rw [hz]
    · exact (Ideal.span {X, Y}).mul_mem_left _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)

end WeierstrassCurve.Affine.TangentNode
end

section EtaleNodeCommonChart


/-! A common etale chart of the original Weierstrass affine scheme and the
literal original-base uniformizer-power node. All maps and initial centre
ideals are retained. Iterated blowup-centre compatibility is not claimed. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Affine.TangentNode WeierstrassCurve.CriticalPoint
open WeierstrassCurve AlgebraicGeometry.Scheme.WeierstrassNode
section CriticalNeighborhoodAPI
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y)

/-- Actual pullback of the original affine coordinates into the common chart. -/
def originalChartMap : (W.toAffine.CoordinateRing) →ₐ[R] TangentChart M.translated :=
  ((IsScalarTower.toAlgHom M.Carrier ((M.translated.toAffine.CoordinateRing))
    (TangentChart M.translated)).restrictScalars R).comp
    (((affineTranslateHom M.baseCurve M.r M.t).restrictScalars R).comp
      (affineCoefficientMap M.Carrier W))

@[simp] theorem originalChartMap_x :
    M.originalChartMap (affineX W) = chartX M.translated +
      algebraMap M.Carrier (TangentChart M.translated) M.r := by
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineTranslateHom M.baseCurve M.r M.t (affineCoefficientMap M.Carrier W (affineX W))) = _
  rw [affineCoefficientMap_x]
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineTranslateHom M.baseCurve M.r M.t (affineX M.baseCurve)) = _
  rw [affineTranslateHom_x]
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineX M.translated + algebraMap M.Carrier ((M.translated.toAffine.CoordinateRing)) M.r) = _
  rw [map_add]
  rfl


@[simp] theorem originalChartMap_y :
    M.originalChartMap (affineY W) = chartY M.translated +
      algebraMap M.Carrier (TangentChart M.translated) M.t := by
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineTranslateHom M.baseCurve M.r M.t (affineCoefficientMap M.Carrier W (affineY W))) = _
  rw [affineCoefficientMap_y]
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineTranslateHom M.baseCurve M.r M.t (affineY M.baseCurve)) = _
  rw [affineTranslateHom_y]
  change algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)
    (affineY M.translated + algebraMap M.Carrier ((M.translated.toAffine.CoordinateRing)) M.t) = _
  rw [map_add]
  rfl


theorem originalChartMap_etale : M.originalChartMap.toRingHom.Etale := by
  let := M.etale
  have h1 := affineCoefficientMap_etale M.Carrier W
  have h2 := RingHom.Etale.of_bijective
    (f := (affineTranslateEquiv M.baseCurve M.r M.t).toRingHom)
    (affineTranslateEquiv M.baseCurve M.r M.t).bijective
  have h3 : (algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart
    M.translated)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  change ((algebraMap ((M.translated.toAffine.CoordinateRing)) (TangentChart M.translated)).comp
    ((affineTranslateHom M.baseCurve M.r M.t).toRingHom.comp
      (affineCoefficientMap M.Carrier W).toRingHom)).Etale
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ h1 h2) h3

/-- A split tangent is expressed in the actual translated residue equation. -/
def SplitTangent (ρ : ResidueField R) : Prop :=
  ρ ^ 2 + (translate (W.map (residue R)) x y).a₁ * ρ -
    (translate (W.map (residue R)) x y).a₂ = 0

variable (he : (W.map (residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : SplitTangent (W := W) (x := x) (y := y) ρ)

/-- The actual original-residue-field point, through the critical translation
and the localized tangent chart. -/
def chartPoint : TangentChart M.translated →ₐ[R] ResidueField R := by
  let : Algebra M.Carrier (ResidueField R) := M.point.toRingHom.toAlgebra
  let : IsScalarTower R M.Carrier (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq (fun r => (M.point.commutes r).symm)
  have h6 : algebraMap M.Carrier (ResidueField R) M.translated.a₆ = 0 :=
    M.point_translated_a6_of_equation he
  have hr : ρ ^ 2 + algebraMap M.Carrier (ResidueField R) M.translated.a₁ * ρ -
      algebraMap M.Carrier (ResidueField R) M.translated.a₂ = 0 := by
    have h1 := congrArg WeierstrassCurve.a₁ M.translated_map_point
    have h2 := congrArg WeierstrassCurve.a₂ M.translated_map_point
    change M.point M.translated.a₁ = _ at h1
    change M.point M.translated.a₂ = _ at h2
    change ρ ^ 2 + M.point M.translated.a₁ * ρ - M.point M.translated.a₂ = 0
    rw [h1, h2]
    exact hρ
  exact (WeierstrassCurve.Affine.TangentNode.chartResidue M.translated h6 ρ hr
    (WeierstrassCurve.Affine.TangentNode.tangent_simple_of_b₂_unit M.translated ρ hr
      M.translated_b2_isUnit)).restrictScalars R

@[simp] theorem chartPoint_x : M.chartPoint he ρ hρ (chartX M.translated) = 0 := by
  simp only [chartPoint, AlgHom.restrictScalars_apply, chartX,
    WeierstrassCurve.Affine.TangentNode.chartResidue_on_tangent,
      WeierstrassCurve.Affine.TangentNode.tangentResidue_x]

@[simp] theorem chartPoint_y : M.chartPoint he ρ hρ (chartY M.translated) = 0 := by
  simp only [chartPoint, AlgHom.restrictScalars_apply, chartY,
    WeierstrassCurve.Affine.TangentNode.chartResidue_on_tangent,
      WeierstrassCurve.Affine.TangentNode.tangentResidue_y]

@[simp] theorem chartPoint_scalar (s : M.Carrier) :
    M.chartPoint he ρ hρ (algebraMap M.Carrier (TangentChart M.translated) s) = M.point s := by
  simp only [chartPoint, AlgHom.restrictScalars_apply, AlgHom.commutes]
  rfl

/-- The original k-rational affine point, with the actual coordinate ring. -/
def originalResidue : (W.toAffine.CoordinateRing) →ₐ[R] ResidueField R :=
  affineLift W x y (by
    simpa only [WeierstrassCurve.Affine.Equation,
      WeierstrassCurve.Affine.evalEval_polynomial,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, ResidueField.algebraMap_eq] using he)

theorem chartPoint_original_triangle :
    (M.chartPoint he ρ hρ).comp M.originalChartMap = originalResidue he := by
  apply affine_ext <;> simp [originalResidue, M.point_r, M.point_t]

/-- Exact pulled-back initial coordinate-centre ideal from the original
residue point. The chosen critical displacement lies in m_R, extended. -/
theorem original_initial_center_eq :
    Ideal.map (algebraMap R (TangentChart M.translated)) (maximalIdeal R) ⊔
      Ideal.span {M.originalChartMap (affineX W) -
          algebraMap R (TangentChart M.translated) M.liftR,
        M.originalChartMap (affineY W) -
          algebraMap R (TangentChart M.translated) M.liftT} =
    Ideal.map (algebraMap R (TangentChart M.translated)) (maximalIdeal R) ⊔
      Ideal.span {AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated
        M.translated_a3 M.translated_a4
          (PlaneNode.U M.translated.a₆),
        AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
          M.translated_a4
          (PlaneNode.V M.translated.a₆)} := by
  have h := M.center_ideal_eq (algebraMap M.Carrier (TangentChart M.translated))
    (M.originalChartMap (affineX W)) (M.originalChartMap (affineY W))
  simp only [Ideal.map_map, ← IsScalarTower.algebraMap_eq R M.Carrier,
    ← IsScalarTower.algebraMap_apply R M.Carrier, M.originalChartMap_x,
    M.originalChartMap_y, add_sub_cancel_right] at h
  rw [M.originalChartMap_x, M.originalChartMap_y]
  exact h.trans (congrArg (fun J =>
    Ideal.map (algebraMap R (TangentChart M.translated)) (maximalIdeal R) ⊔ J)
    (chart_origin_ideal_eq M.translated M.translated_a3 M.translated_a4))

variable (c : R) (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier c)

/-- Unit removal followed by the literal original-base node coefficient map. -/
def powerChartMap : PlaneNode.Ring c →ₐ[R] TangentChart M.translated :=
  ((AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
    M.translated_a4).restrictScalars R).comp
    (((PlaneNode.scaledEquiv (algebraMap R M.Carrier c) a M.translated.a₆
      ha).symm.toAlgHom.restrictScalars R).comp
      (PlaneNode.coefficientMap M.Carrier c))

@[simp] theorem powerChartMap_u :
    M.powerChartMap c a ha (PlaneNode.U c) =
      algebraMap M.Carrier (TangentChart M.translated) (↑a⁻¹ : M.Carrier) *
        AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
          M.translated_a4 (PlaneNode.U M.translated.a₆) := by
  simp [powerChartMap]

@[simp] theorem powerChartMap_v :
    M.powerChartMap c a ha (PlaneNode.V c) =
      AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
        M.translated_a4 (PlaneNode.V M.translated.a₆) := by
  simp [powerChartMap]

theorem powerChartMap_etale : (M.powerChartMap c a ha).toRingHom.Etale := by
  let := M.etale
  have h1 := PlaneNode.coefficientMap_etale M.Carrier c
  have h2 := RingHom.Etale.of_bijective
    (f := (PlaneNode.scaledEquiv (algebraMap R M.Carrier c) a M.translated.a₆ ha).symm.toRingHom)
    (PlaneNode.scaledEquiv (algebraMap R M.Carrier c) a M.translated.a₆ ha).symm.bijective
  have h3 : (AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
    M.translated_a4).toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (AlgebraicGeometry.Scheme.WeierstrassNode.toNode_etale M.translated M.translated_a3
        M.translated_a4)
  change ((AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
    M.translated_a4).toRingHom.comp
    ((PlaneNode.scaledEquiv (algebraMap R M.Carrier c) a M.translated.a₆ ha).symm.toRingHom.comp
      (PlaneNode.coefficientMap M.Carrier c).toRingHom)).Etale
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ h1 h2) h3

include he ha in
theorem node_parameter_residue_zero : residue R c = 0 := by
  have h := congrArg M.point ha
  simp only [M.point_translated_a6_of_equation he, map_mul, M.point_structure] at h
  apply (a.isUnit.map M.point).mul_left_cancel
  simpa only [mul_zero] using h.symm

theorem chartPoint_power_triangle :
    (M.chartPoint he ρ hρ).comp (M.powerChartMap c a ha) =
      PlaneNode.residueMap c (M.node_parameter_residue_zero he c a ha) := by
  apply PlaneNode.hom_ext <;> simp [PlaneNode.residueMap]

/-- Equality of the two actual initial-centre pullbacks, including the unit
rescaling on the original-base node side. -/
theorem initial_center_power_eq :
    Ideal.map (algebraMap R (TangentChart M.translated)) (maximalIdeal R) ⊔
      Ideal.span {M.originalChartMap (affineX W) -
          algebraMap R (TangentChart M.translated) M.liftR,
        M.originalChartMap (affineY W) -
          algebraMap R (TangentChart M.translated) M.liftT} =
    Ideal.map (algebraMap R (TangentChart M.translated)) (maximalIdeal R) ⊔
      Ideal.span {M.powerChartMap c a ha (PlaneNode.U c), M.powerChartMap c a ha (PlaneNode.V c)}
        := by
  rw [M.original_initial_center_eq, M.powerChartMap_u, M.powerChartMap_v]
  congr 1
  have h := unit_scale_coordinate_ideal_eq
    (AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
      M.translated_a4 (PlaneNode.U M.translated.a₆))
    (AlgebraicGeometry.Scheme.WeierstrassNode.nodeChartMap M.translated M.translated_a3
      M.translated_a4 (PlaneNode.V M.translated.a₆))
    (Units.map (algebraMap M.Carrier (TangentChart M.translated)) a⁻¹)
  exact h

/-- The ideal in the original affine coordinate ring generated by the base maximal ideal
and the coordinate differences from the chosen lifts `M.liftR` and `M.liftT`. -/
def originalCenter : Ideal ((W.toAffine.CoordinateRing)) :=
  Ideal.map (algebraMap R ((W.toAffine.CoordinateRing))) (maximalIdeal R) ⊔
    Ideal.span {affineX W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftR,
      affineY W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftT}

theorem initial_center_pullback_eq :
    Ideal.map M.originalChartMap.toRingHom M.originalCenter =
      Ideal.map (M.powerChartMap c a ha).toRingHom (PlaneNode.residueCenter c) := by
  simp only [originalCenter, PlaneNode.residueCenter, Ideal.map_sup, Ideal.map_map,
    Ideal.map_span, Set.image_insert_eq, Set.image_singleton, AlgHom.toRingHom_eq_coe]
  rw [M.originalChartMap.comp_algebraMap, (M.powerChartMap c a ha).comp_algebraMap]
  simpa only [AlgHom.coe_toRingHom, map_sub, AlgHom.commutes] using
    M.initial_center_power_eq c a ha


/-- The spectrum of the localized tangent chart of the critically translated curve. -/
abbrev commonScheme := AlgebraicGeometry.Scheme.WeierstrassNode.CommonChart M.translated

/-- The étale morphism from the common chart to the original affine Weierstrass scheme,
induced by coefficient extension and the critical translation. -/
def toOriginalScheme : M.commonScheme ⟶ AffineScheme W :=
  Spec.map (CommRingCat.ofHom M.originalChartMap.toRingHom)

/-- The étale morphism from the common chart to `Spec (PlaneNode.Ring c)`, induced by
the split tangent coordinates and removal of the unit factor in the translated `a₆`. -/
def toPowerNodeScheme : M.commonScheme ⟶ Spec (.of (PlaneNode.Ring c)) :=
  Spec.map (CommRingCat.ofHom (M.powerChartMap c a ha).toRingHom)

/-- The point of the common chart valued in the original residue field, using the residue
solution `(x, y)` and the chosen split tangent root `ρ`. -/
def commonResiduePoint : Spec (.of (ResidueField R)) ⟶ M.commonScheme :=
  Spec.map (CommRingCat.ofHom (M.chartPoint he ρ hρ).toRingHom)

instance toOriginalScheme_etale : Etale M.toOriginalScheme :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr M.originalChartMap_etale

instance toPowerNodeScheme_etale : Etale (M.toPowerNodeScheme c a ha) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (M.powerChartMap_etale c a ha)

theorem original_structure_triangle :
    M.toOriginalScheme ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((W.toAffine.CoordinateRing)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TangentChart M.translated))) := by
  rw [toOriginalScheme, ← Spec.map_comp]
  congr 1
  ext r
  exact M.originalChartMap.commutes r

theorem power_structure_triangle :
    M.toPowerNodeScheme c a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring c))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TangentChart M.translated))) := by
  rw [toPowerNodeScheme, ← Spec.map_comp]
  congr 1
  ext r
  exact (M.powerChartMap c a ha).commutes r

theorem residue_original_triangle :
    M.commonResiduePoint he ρ hρ ≫ M.toOriginalScheme =
      Spec.map (CommRingCat.ofHom (originalResidue he).toRingHom) := by
  rw [commonResiduePoint, toOriginalScheme, ← Spec.map_comp]
  exact congrArg (fun f : (W.toAffine.CoordinateRing) →ₐ[R] ResidueField R =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (M.chartPoint_original_triangle he ρ hρ)

theorem residue_power_triangle :
    M.commonResiduePoint he ρ hρ ≫ M.toPowerNodeScheme c a ha =
      Spec.map (CommRingCat.ofHom (PlaneNode.residueMap c
        (M.node_parameter_residue_zero he c a ha)).toRingHom) := by
  rw [commonResiduePoint, toPowerNodeScheme, ← Spec.map_comp]
  exact congrArg (fun f : PlaneNode.Ring c →ₐ[R] ResidueField R =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (M.chartPoint_power_triangle he ρ hρ c a ha)

end CriticalNeighborhoodAPI
end WeierstrassCurve.CriticalNeighborhood

end
end EtaleNodeCommonChart

section NodePointCenters


/-! The initial coordinate-centre ideals are the actual residue-point kernels
on the two affine schemes. No assertion about centres after blowups is made. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open IsLocalRing
namespace WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Affine.TangentNode
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y)

theorem originalCenter_eq_point_kernel
    (he : (W.map (residue R)).toAffine.Equation x y) :
    M.originalCenter = RingHom.ker (originalResidue he).toRingHom := by
  let I := M.originalCenter
  let Q := (W.toAffine.CoordinateRing) ⧸ I
  let q : (W.toAffine.CoordinateRing) →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let p := originalResidue he
  have hz (r : R) (hr : r ∈ maximalIdeal R) : algebraMap R Q r = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (show algebraMap R ((W.toAffine.CoordinateRing)) r ∈ I from
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr))
  let j : ResidueField R →ₐ[R] Q :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R Q) hz
  have hqx : q (affineX W) = algebraMap R Q M.liftR := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I (affineX W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftR) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have hqy : q (affineY W) = algebraMap R Q M.liftT := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I (affineY W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftT) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have hmaps : q = j.comp p := by
    apply affine_ext
    · simp only [AlgHom.comp_apply, p, originalResidue, affineLift_x]
      rw [hqx]
      exact (j.commutes M.liftR).symm.trans (congrArg j M.residue_lift_r)
    · simp only [AlgHom.comp_apply, p, originalResidue, affineLift_y]
      rw [hqy]
      exact (j.commutes M.liftT).symm.trans (congrArg j M.residue_lift_t)
  have hle : I ≤ RingHom.ker p.toRingHom := by
    refine sup_le ?_ (Ideal.span_le.mpr ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change p (algebraMap R ((W.toAffine.CoordinateRing)) r) = 0
      rw [p.commutes, ResidueField.algebraMap_eq]
      exact (residue_eq_zero_iff r).mpr hr
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]
        change p (affineX W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftR) = 0
        simp only [p, originalResidue, map_sub, affineLift_x, AlgHom.commutes,
          ResidueField.algebraMap_eq, M.residue_lift_r, sub_self]
      · rw [hz]
        change p (affineY W - algebraMap R ((W.toAffine.CoordinateRing)) M.liftT) = 0
        simp only [p, originalResidue, map_sub, affineLift_y, AlgHom.commutes,
          ResidueField.algebraMap_eq, M.residue_lift_t, sub_self]
  refine le_antisymm hle ?_
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q z = 0
  change p z = 0 at hz
  rw [hmaps, AlgHom.comp_apply, hz, map_zero]

/-- The ideal equality is an equality of the actual two residue-point kernels
pulled back along the actual chart maps. -/
theorem residue_point_kernel_pullback_eq
    (he : (W.map (residue R)).toAffine.Equation x y)
    (c : R) (a : M.Carrierˣ)
    (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier c) :
    Ideal.map M.originalChartMap.toRingHom
        (RingHom.ker (originalResidue he).toRingHom) =
      Ideal.map (M.powerChartMap c a ha).toRingHom
        (RingHom.ker (PlaneNode.residueMap c (M.node_parameter_residue_zero he c a ha)).toRingHom)
          := by
  rw [← M.originalCenter_eq_point_kernel he, ← PlaneNode.residueCenter_eq_ker]
  exact M.initial_center_pullback_eq c a ha


end WeierstrassCurve.CriticalNeighborhood

end
end NodePointCenters
