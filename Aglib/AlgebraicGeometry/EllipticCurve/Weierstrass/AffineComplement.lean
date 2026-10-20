/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineChart
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The exact infinity complement of the affine chart

Source: ordinary R5 Weierstrass.Projective, lines 730–928.
Over a field the standard affine chart misses exactly the rational
point represented by (0:1:0). No nonsingularity is needed.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MvPolynomial MonoidalCategory
namespace WeierstrassCurve.Projective
universe u
attribute [local instance] Over.cartesianMonoidalCategory

section Ring
variable {k : Type u} [CommRing k]

lemma normalizePolynomial_surjective (W : WeierstrassCurve k) (i : Fin 3) :
    Function.Surjective (normalizePolynomial W i) := by
  intro a
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W i) a
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hb
  exact ⟨p, normalizePolynomial_homogeneous W i p (by simpa using hp)⟩

@[simp] lemma infinityChartEval_normalizedCoordinate (W : WeierstrassCurve k) (j : Fin 3) :
    infinityChartEval W (normalizedCoordinate W 1 j) = ![0, 1, 0] j := by
  rw [normalizedCoordinate, infinityChartEval_mk, infinityEval_coordinate]

@[simp] lemma infinityChartEval_chartConstant (W : WeierstrassCurve k) (a : k) :
    infinityChartEval W (chartConstant W 1 a) = a :=
  infinityChartEval_constant W a

lemma coordinate_generate (W : WeierstrassCurve k) :
    Algebra.adjoin (grading W 0) (Set.range (coordinate W)) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (constToGradeZero W a)
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨j, rfl⟩)

lemma exists_coordinate_not_mem (W : WeierstrassCurve k) (p : scheme W) :
    ∃ i : Fin 3, coordinate W i ∉ p.asHomogeneousIdeal := by
  have h := Proj.iSup_basicOpen_eq_top' (grading W) (coordinate W)
    (fun i => ⟨1, coordinate_mem W i⟩) (coordinate_generate W)
  have hp : p ∈ (⨆ i : Fin 3, Proj.basicOpen (grading W) (coordinate W i)) := by
    rw [h]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hp

lemma coordinate_cubic (W : WeierstrassCurve k) :
    coordinate W 1 ^ 2 * coordinate W 2 +
      algebraMap k (homogeneousCoordinateRing W) W.a₁ * coordinate W 0 * coordinate W 1 *
        coordinate W 2 +
      algebraMap k (homogeneousCoordinateRing W) W.a₃ * coordinate W 1 * coordinate W 2 ^ 2 -
      (coordinate W 0 ^ 3 + algebraMap k (homogeneousCoordinateRing W) W.a₂ *
        coordinate W 0 ^ 2 * coordinate W 2 + algebraMap k (homogeneousCoordinateRing W) W.a₄ *
        coordinate W 0 * coordinate W 2 ^ 2 + algebraMap k (homogeneousCoordinateRing W) W.a₆ *
        coordinate W 2 ^ 3) = 0 := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton W.toProjective.polynomial) :
      W.toProjective.polynomial ∈ cubicIdeal W)
  simp only [WeierstrassCurve.Projective.polynomial] at h
  convert h using 1 <;> rfl

lemma coordinate_x_mem_of_z_mem (W : WeierstrassCurve k) (p : scheme W)
    (hz : coordinate W 2 ∈ p.asHomogeneousIdeal) : coordinate W 0 ∈ p.asHomogeneousIdeal := by
  let q := Ideal.Quotient.mk p.asHomogeneousIdeal.toIdeal
  have hz' : q (coordinate W 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have h := congrArg q (coordinate_cubic W)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, hz',
    mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    sub_eq_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero h.symm)

lemma coordinate_y_not_mem_of_z_mem (W : WeierstrassCurve k) (p : scheme W)
    (hz : coordinate W 2 ∈ p.asHomogeneousIdeal) : coordinate W 1 ∉ p.asHomogeneousIdeal := by
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem W p
  fin_cases i
  · exact False.elim (hi (coordinate_x_mem_of_z_mem W p hz))
  · exact hi
  · exact False.elim (hi hz)

lemma basicOpenToSpec_lrs (W : WeierstrassCurve k) (i : Fin 3) :
    Scheme.forgetToLocallyRingedSpace.map
      (Proj.basicOpenToSpec (grading W) (coordinate W i)) =
      ProjectiveSpectrum.Proj.toSpec (grading W) (coordinate W i) := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma chart_eq_fromSpec (W : WeierstrassCurve k) (i : Fin 3)
    (p : Spec (.of (chartRing W i))) :
    chart W i p =
      (ProjIsoSpecTopComponent.FromSpec.toFun (coordinate_mem W i) (by decide) p).val := by
  let e := Proj.basicOpenIsoSpec (grading W) (coordinate W i) (coordinate_mem W i) (by decide)
  change (e.inv p).val = _
  apply congrArg Subtype.val
  apply ProjIsoSpecTopComponent.toSpec_injective (grading W) (coordinate_mem W i) (by decide)
  rw [ProjIsoSpecTopComponent.toSpec_fromSpec]
  rw [← ProjectiveSpectrum.Proj.toSpec_base_apply_eq]
  rw [← basicOpenToSpec_lrs]
  change e.hom (e.inv p) = p
  exact congrArg (fun f => f p) e.inv_hom_id

lemma coordinate_mem_chart_iff (W : WeierstrassCurve k) (i j : Fin 3)
    (p : Spec (.of (chartRing W i))) :
    coordinate W j ∈ (chart W i p).asHomogeneousIdeal ↔
      normalizedCoordinate W i j ∈ p.asIdeal := by
  rw [chart_eq_fromSpec]
  convert ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff
    (coordinate_mem W i) (by decide) p
    ⟨1, ⟨coordinate W j, coordinate_mem W j⟩, ⟨coordinate W i, coordinate_mem W i⟩,
      Submonoid.mem_powers _⟩ using 1
  · rfl
  · apply Iff.of_eq
    congr 1
    apply HomogeneousLocalization.val_injective
    simp [normalizedCoordinate]
end Ring
section Field
variable {k : Type u} [Field k]

lemma infinityChart_prime_unique (W : WeierstrassCurve k) (p : PrimeSpectrum (chartRing W 1))
    (hx : normalizedCoordinate W 1 0 ∈ p.asIdeal)
    (hz : normalizedCoordinate W 1 2 ∈ p.asIdeal) :
    p.asIdeal = RingHom.ker (infinityChartEval W) := by
  let q := Ideal.Quotient.mk p.asIdeal
  have hx' : q (normalizedCoordinate W 1 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hz' : q (normalizedCoordinate W 1 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  let c : k →+* chartRing W 1 ⧸ p.asIdeal := q.comp (chartConstant W 1)
  have h : q.comp (normalizePolynomial W 1) =
      (c.comp (infinityChartEval W)).comp (normalizePolynomial W 1) := by
    ext a
    · simp [normalizePolynomial, c]
    · fin_cases a <;> simp [normalizePolynomial, hx', hz', c]
  have hq (a : chartRing W 1) : q a = c (infinityChartEval W a) := by
    obtain ⟨r, rfl⟩ := normalizePolynomial_surjective W 1 a
    exact congrArg (fun f : MvPolynomial (Fin 3) k →+* chartRing W 1 ⧸ p.asIdeal => f r) h
  ext a
  change a ∈ p.asIdeal ↔ infinityChartEval W a = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem, hq]
  exact map_eq_zero_iff c c.injective


/-- The point of the projective cubic represented by `(0:1:0)` over a field. -/
def infinityPoint (W : WeierstrassCurve k) : scheme W :=
  infinitySection W (IsLocalRing.closedPoint k)

/-- The point represented by `(0:1:0)` in the second standard affine chart. -/
def infinityChartPoint (W : WeierstrassCurve k) : Spec (.of (chartRing W 1)) :=
  Spec.map (CommRingCat.ofHom (infinityChartEval W)) (IsLocalRing.closedPoint k)

lemma infinityChartPoint_asIdeal (W : WeierstrassCurve k) :
    (infinityChartPoint W).asIdeal = RingHom.ker (infinityChartEval W) := by
  change Ideal.comap (infinityChartEval W) (IsLocalRing.maximalIdeal k) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

lemma infinityPoint_eq_chart (W : WeierstrassCurve k) :
    infinityPoint W = chart W 1 (infinityChartPoint W) := rfl

lemma infinityPoint_z_mem (W : WeierstrassCurve k) :
    coordinate W 2 ∈ (infinityPoint W).asHomogeneousIdeal := by
  rw [infinityPoint_eq_chart, coordinate_mem_chart_iff, infinityChartPoint_asIdeal]
  simp [RingHom.mem_ker]

lemma eq_infinityPoint_of_z_mem (W : WeierstrassCurve k) (p : scheme W)
    (hz : coordinate W 2 ∈ p.asHomogeneousIdeal) : p = infinityPoint W := by
  have hy : p ∈ (chart W 1).opensRange := by
    rw [chart_range]
    exact coordinate_y_not_mem_of_z_mem W p hz
  obtain ⟨q, rfl⟩ := hy
  have hx := (coordinate_mem_chart_iff W 1 0 q).mp
    (coordinate_x_mem_of_z_mem W (chart W 1 q) hz)
  have hz' := (coordinate_mem_chart_iff W 1 2 q).mp hz
  have hq : q = infinityChartPoint W := by
    apply PrimeSpectrum.ext
    rw [infinityChart_prime_unique W q hx hz', infinityChartPoint_asIdeal]
  rw [hq, ← infinityPoint_eq_chart]

/-- The standard affine chart misses exactly the actual point (0:1:0). -/
lemma affineChart_range_complement (W : WeierstrassCurve k) :
    Set.range (affineChart W : Spec (.of (affineRing W)) → scheme W) =
      {p : scheme W | p ≠ infinityPoint W} := by
  ext p
  change p ∈ (affineChart W).opensRange ↔ p ≠ infinityPoint W
  rw [affineChart_range, Proj.mem_basicOpen]
  constructor
  · intro hz hp
    rw [hp] at hz
    exact hz (infinityPoint_z_mem W)
  · intro hp hz
    exact hp (eq_infinityPoint_of_z_mem W p hz)

/-- The actual affine Weierstrass spectrum with its structural map. -/
def affineOver (W : WeierstrassCurve k) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))))

/-- The canonical affine Weierstrass chart as a morphism over the base field. -/
def affineChartOver (W : WeierstrassCurve k) : affineOver W ⟶ curveOver W :=
  Over.homMk (affineChart W) (affineChart_structure W)

/-- The standard infinity section as a rational point of the same cubic. -/
def originOver (W : WeierstrassCurve k) : 𝟙_ (Scheme.OverField.FScheme k) ⟶ curveOver W :=
  Over.homMk (infinitySection W) (infinitySection_structure W)

end Field

end WeierstrassCurve.Projective
