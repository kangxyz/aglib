/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.InfinityRing
public import Aglib.AlgebraicGeometry.Curves.Nodal.Gluing
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement
public import Aglib.RingTheory.Localization.Away.MapInverse
public import Aglib.RingTheory.Spectrum.Prime.BasicOpenUnit

/-!
# Full overlaps of the adapted critical-cubic charts

The original affine chart and the chart away from Y−rX cover the same Proj.
Their maps agree on the entire conductor localization, with reciprocal
parameter w=1/u, and both inverse images are exactly the stated overlap opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u

namespace WeierstrassCurve.CriticalCubic.AdaptedInfinity

open WeierstrassCurve.Projective
variable (k : Type u) [Field k] (a b r : k)
local notation "W" => CriticalCubic.equation k a b
local notation "H" => homogeneousCoordinateRing W
local notation "V" => Polynomial.PinchedPair.infinityChartRing k

/-- The original Proj inclusion for the actual homogeneous form Y-rX. -/
def projectiveChart : Spec (.of (ChartRing k a b r)) ⟶ scheme W :=
  Proj.awayι (grading W) (denominator k a b r) (denominator_mem k a b r) (by decide)

/-- The homogeneous chart away from `Y - rX` is open in the critical cubic. -/
instance projectiveChart_open : IsOpenImmersion (projectiveChart k a b r) := by
  unfold projectiveChart
  infer_instance

/-- The standard infinity affine scheme, included using the proved ring inverse. -/
def infinityChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Spec (.of V) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs)) ≫ projectiveChart k a b r

/-- For the supplied distinct tangent roots, the adapted infinity chart is an open immersion. -/
instance infinityChart_open (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    IsOpenImmersion (infinityChart k a b r s hrs hr hs) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs))) := by
    change IsIso (Scheme.Spec.mapIso (ringEquiv k a b r s hrs hr hs).symm.toCommRingCatIso.op).hom
    infer_instance
  unfold infinityChart
  infer_instance

lemma infinityChart_range (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (infinityChart k a b r s hrs hr hs).opensRange =
      Proj.basicOpen (grading W) (denominator k a b r) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs))) := by
    change IsIso (Scheme.Spec.mapIso (ringEquiv k a b r s hrs hr hs).symm.toCommRingCatIso.op).hom
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (Proj.opensRange_awayι _ _ (denominator_mem k a b r) (by decide))

@[reassoc] lemma infinityChart_structure (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    infinityChart k a b r s hrs hr hs ≫ structureMap W =
      Spec.algebraMap k V := by
  rw [infinityChart, projectiveChart, structureMap, Category.assoc,
    ← Category.assoc _ (Proj.toSpecZero _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact fromChart_scalar k a b r s hrs hr hs c

lemma denominator_not_mem_of_z_mem (p : scheme W)
    (hz : coordinate W 2 ∈ p.asHomogeneousIdeal) :
    denominator k a b r ∉ p.asHomogeneousIdeal := by
  intro hL
  apply coordinate_y_not_mem_of_z_mem W p hz
  have hx := coordinate_x_mem_of_z_mem W p hz
  have h := p.asHomogeneousIdeal.toIdeal.add_mem hL
    (p.asHomogeneousIdeal.toIdeal.mul_mem_left (algebraMap k H r) hx)
  change coordinate W 1 ∈ p.asHomogeneousIdeal.toIdeal
  simpa only [denominator, sub_add_cancel] using h

/-- The adapted infinity chart and the identical original affine chart cover Proj. -/
lemma infinity_affine_cover (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (infinityChart k a b r s hrs hr hs).opensRange ⊔ (affineChart W).opensRange = ⊤ := by
  apply top_unique
  intro p _
  classical
  by_cases hz : coordinate W 2 ∈ p.asHomogeneousIdeal
  · exact Or.inl (by
      rw [infinityChart_range]
      exact denominator_not_mem_of_z_mem k a b r p hz)
  · exact Or.inr (by rw [affineChart_range]; exact hz)

/-- The node chart included by the explicit affine equivalence. -/
def nodeChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Scheme.PinchedLine.nodeScheme k ⟶ scheme W :=
  (CriticalCubic.coordinateNodeSchemeIso k a b r s hrs hr hs).inv ≫ affineChart W

/-- For the supplied distinct tangent roots, the pinched affine chart maps openly to the
critical cubic. -/
instance nodeChart_open (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    IsOpenImmersion (nodeChart k a b r s hrs hr hs) := by
  unfold nodeChart
  infer_instance

lemma nodeChart_range (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (nodeChart k a b r s hrs hr hs).opensRange = Proj.basicOpen (grading W) (coordinate W 2) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (affineChart_range W)

@[reassoc] lemma nodeChart_structure (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    nodeChart k a b r s hrs hr hs ≫ structureMap W =
      Spec.algebraMap k (Polynomial.PinchedPair.nodeRing k) := by
  rw [nodeChart, Category.assoc, affineChart_structure]
  exact CriticalCubic.coordinateNodeSchemeIso_inv_over k a b r s hrs hr hs

lemma node_infinity_cover (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (nodeChart k a b r s hrs hr hs).opensRange ⊔
      (infinityChart k a b r s hrs hr hs).opensRange = ⊤ := by
  rw [sup_comm, nodeChart_range, ← affineChart_range W]
  exact infinity_affine_cover k a b r s hrs hr hs

/-! Ordinary localization restricted to the literal degree-zero subring. This is
only a map construction and its universal-property equality, not a geometric family. -/
section Evaluation
variable {S : Type u} [CommRing S]

/-- Evaluation of a homogeneous chart in a ring where the image of its denominator is a unit. -/
def evaluateChart (d : H) (f : H →+* S) (hf : IsUnit (f d)) :
    HomogeneousLocalization.Away (grading W) d →+* S :=
  (Localization.awayLift f d hf).comp
    (algebraMap (HomogeneousLocalization.Away (grading W) d) (Localization.Away d))

lemma evaluateChart_mk (d : H) (hd : d ∈ grading W 1) (f : H →+* S)
    (hf : IsUnit (f d)) (v : S) (hv : f d * v = 1) (n : ℕ) (z : H)
    (hz : z ∈ grading W (n • 1)) :
    evaluateChart k a b d f hf (HomogeneousLocalization.Away.mk (grading W) hd n z hz) =
      f z * v ^ n := by
  simpa only [evaluateChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk] using Localization.awayLift_mk f d z v hv n

lemma evaluateChart_mk_mul (d : H) (hd : d ∈ grading W 1) (f : H →+* S)
    (hf : IsUnit (f d)) (n : ℕ) (z : H) (hz : z ∈ grading W (n • 1)) :
    evaluateChart k a b d f hf (HomogeneousLocalization.Away.mk (grading W) hd n z hz) *
      f d ^ n = f z := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hf
  rw [evaluateChart_mk k a b d hd f hf v hv]
  calc
    f z * v ^ n * f d ^ n = f z * (f d * v) ^ n := by ring
    _ = f z := by rw [hv, one_pow, mul_one]

lemma evaluateChart_fromZero (d : H) (f : H →+* S) (hf : IsUnit (f d))
    (c : grading W 0) :
    evaluateChart k a b d f hf (HomogeneousLocalization.fromZeroRingHom (grading W) _ c) =
      f c := by
  simp only [evaluateChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  change Localization.awayLift f d hf (Localization.mk (c : H) 1) = f c
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]

lemma evaluateChart_awayMap (d e x : H) (he : e ∈ grading W 1) (hx : x = d * e)
    (f : H →+* S) (hd : IsUnit (f d)) (hfx : IsUnit (f x)) :
    (evaluateChart k a b x f hfx).comp (HomogeneousLocalization.awayMap (grading W) he hx) =
      evaluateChart k a b d f hd := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply, evaluateChart, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_awayMap]
  have h : (Localization.awayLift f x hfx).comp
      (Localization.awayLift (algebraMap H (Localization.Away x)) d
        (isUnit_of_dvd_unit (map_dvd _ ⟨e, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))) =
      Localization.awayLift f d hd := by
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, Localization.awayLift, IsLocalization.Away.lift_eq]
  exact congrArg (fun g : Localization.Away d →+* S => g z.val) h

/-- The two evaluations land in the same existing projective scheme morphism,
proved through the actual product homogeneous localization. -/
lemma evaluateChart_projective_eq (d e : H) (hd : d ∈ grading W 1) (he : e ∈ grading W 1)
    (f : H →+* S) (hfd : IsUnit (f d)) (hfe : IsUnit (f e)) :
    Spec.map (CommRingCat.ofHom (evaluateChart k a b d f hfd)) ≫
        Proj.awayι (grading W) d hd (by decide) =
      Spec.map (CommRingCat.ofHom (evaluateChart k a b e f hfe)) ≫
        Proj.awayι (grading W) e he (by decide) := by
  let hfde : IsUnit (f (d * e)) := by rw [map_mul]; exact hfd.mul hfe
  rw [← evaluateChart_awayMap k a b d e (d * e) he rfl f hfd hfde,
    ← evaluateChart_awayMap k a b e d (d * e) hd (mul_comm d e) f hfe hfde]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

end Evaluation

/-- The actual standard infinity origin, w=0 in k[w,(w-1)⁻¹]. -/
def standardOrigin : V →+* k :=
  Localization.awayLift (Polynomial.evalRingHom (0 : k)) (Polynomial.X - 1) (by simp)

@[simp] lemma standardOrigin_polynomial (p : k[X]) :
    standardOrigin k (algebraMap k[X] V p) = p.eval 0 := by
  unfold standardOrigin
  exact IsLocalization.Away.lift_eq (g := Polynomial.evalRingHom (0 : k))
    (Polynomial.X - 1 : k[X]) (by simp) p

@[simp] lemma standardOrigin_scalar (c : k) : standardOrigin k (algebraMap k V c) = c := by
  change standardOrigin k (algebraMap k[X] V (Polynomial.C c)) = c
  rw [standardOrigin_polynomial, Polynomial.eval_C]

@[simp] lemma standardOrigin_parameter : standardOrigin k (standardParameter k) = 0 := by
  rw [standardParameter, standardOrigin_polynomial, Polynomial.eval_X]

lemma standardOrigin_dehomogenize (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (standardOrigin k).comp (dehomogenize k a b r s hrs hr hs) = infinityEval W := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [dehomogenize, infinityEval]
  · intro i
    fin_cases i <;> simp [dehomogenize, infinityEval, xValue, yValue, zValue]

lemma standardOrigin_fromChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (standardOrigin k).comp (fromChart k a b r s hrs hr hs) =
      evaluateChart k a b (denominator k a b r) (infinityEval W)
        (by simp [denominator]) := by
  apply RingHom.ext
  intro z
  obtain ⟨n, z, hz, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (denominator_mem k a b r) z
  rw [RingHom.comp_apply, fromChart_mk,
    evaluateChart_mk k a b _ (denominator_mem k a b r) _ _ 1 (by simp [denominator])]
  simpa only [one_pow, mul_one, RingHom.comp_apply] using
    congrArg (fun f : H →+* k => f z) (standardOrigin_dehomogenize k a b r s hrs hr hs)

/-- A scheme-morphism equality with the permanent infinity section, not just coordinates. -/
@[reassoc] lemma infinityChart_origin (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Spec.map (CommRingCat.ofHom (standardOrigin k)) ≫ infinityChart k a b r s hrs hr hs =
      infinitySection W := by
  rw [infinityChart, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((standardOrigin k).comp (fromChart k a b r s hrs hr hs))) ≫
      projectiveChart k a b r = infinitySection W
  rw [standardOrigin_fromChart]
  exact evaluateChart_projective_eq k a b (denominator k a b r) (coordinate W 1)
    (denominator_mem k a b r) (coordinate_mem W 1) (infinityEval W)
    (by simp [denominator]) (by simp)

end WeierstrassCurve.CriticalCubic.AdaptedInfinity

namespace WeierstrassCurve.CriticalCubic.AdaptedInfinity

open WeierstrassCurve.Projective
variable (k : Type u) [Field k] (a b r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0)
local notation "W" => CriticalCubic.equation k a b
local notation "H" => homogeneousCoordinateRing W
local notation "V" => Polynomial.PinchedPair.infinityChartRing k
local notation "O" => Polynomial.PinchedPair.ConductorReciprocal.W k
open Polynomial.PinchedPair.ConductorReciprocal

/-- The actual accepted affine coordinate map, restricted to the permanent overlap. -/
def overlapAffine : affineRing W →ₐ[k] O :=
  (Polynomial.PinchedPair.affineOverlapRingMap k).comp
    (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs).toAlgHom

/-- Original homogeneous coordinates on the Z=1 side of the genuine overlap. -/
def overlapEval : H →+* O :=
  (overlapAffine k a b r s hrs hr hs).toRingHom.comp (WeierstrassCurve.Projective.dehomogenize W)

@[simp] lemma overlapEval_scalar (c : k) :
    overlapEval k a b r s hrs hr hs (algebraMap k H c) = algebraMap k O c := by
  simp [overlapEval]

@[simp] lemma overlapEval_z : overlapEval k a b r s hrs hr hs (coordinate W 2) = 1 := by
  simp [overlapEval]

lemma overlapEval_x : overlapEval k a b r s hrs hr hs (coordinate W 0) =
    algebraMap k O (s - r) ^ 2 * algebraMap k[X] O (q k) := by
  simp only [overlapEval, RingHom.comp_apply, WeierstrassCurve.Projective.dehomogenize_coordinate,
    Matrix.cons_val_zero]
  change Polynomial.PinchedPair.affineOverlapRingMap k
    (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs (affineX W)) = _
  rw [CriticalCubic.coordinateNodeEquiv_X, map_mul, AlgHom.commutes]
  change algebraMap k O ((s - r) ^ 2) * algebraMap k[X] O (q k) =
    algebraMap k O (s - r) ^ 2 * algebraMap k[X] O (q k)
  rw [map_pow]

lemma overlapEval_y : overlapEval k a b r s hrs hr hs (coordinate W 1) =
    algebraMap k O r * algebraMap k O (s - r) ^ 2 * algebraMap k[X] O (q k) +
      algebraMap k O (s - r) ^ 3 * algebraMap k[X] O (q k) * t k := by
  simp only [overlapEval, RingHom.comp_apply, WeierstrassCurve.Projective.dehomogenize_coordinate,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  change Polynomial.PinchedPair.affineOverlapRingMap k
    (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs (affineY W)) = _
  rw [CriticalCubic.coordinateNodeEquiv_Y]
  simp only [map_add, map_mul, map_pow, AlgHom.commutes]
  change algebraMap k O r * algebraMap k O (s - r) ^ 2 * algebraMap k[X] O (q k) +
    algebraMap k O (s - r) ^ 3 * algebraMap k[X] O (q k * Polynomial.X) = _
  rw [map_mul]
  simp only [t]
  ring

lemma overlapEval_denominator : overlapEval k a b r s hrs hr hs (denominator k a b r) =
    algebraMap k O (s - r) ^ 3 * algebraMap k[X] O (q k) * t k := by
  rw [denominator, map_sub, map_mul, overlapEval_scalar, overlapEval_x, overlapEval_y]
  ring

lemma overlapEval_denominator_isUnit :
    IsUnit (overlapEval k a b r s hrs hr hs (denominator k a b r)) := by
  rw [overlapEval_denominator]
  exact (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hrs.symm)).map (algebraMap k O)).pow 3).mul
    (IsLocalization.Away.algebraMap_isUnit (q k)) |>.mul
      (isUnit_iff_exists_inv.mpr ⟨invT k, t_mul_invT k⟩)

lemma overlap_evaluate_affine :
    evaluateChart k a b (coordinate W 2) (overlapEval k a b r s hrs hr hs) (by simp) =
      (overlapAffine k a b r s hrs hr hs).toRingHom.comp (fromProjectiveChart W) := by
  apply RingHom.ext
  intro z
  obtain ⟨n, z, hz, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W 2) z
  rw [RingHom.comp_apply, fromProjectiveChart_mk,
    evaluateChart_mk k a b _ (coordinate_mem W 2) _ _ 1 (by simp)]
  simp only [one_pow, mul_one]
  rfl

lemma overlap_evaluate_scalar (c : k) :
    evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
      (overlapEval_denominator_isUnit k a b r s hrs hr hs) (scalar k a b r c) = algebraMap k O c
        := by
  rw [scalar, RingHom.comp_apply, evaluateChart_fromZero]
  exact overlapEval_scalar k a b r s hrs hr hs c

/-- Literal reciprocal-coordinate equality w=1/u in the permanent overlap ring. -/
lemma overlap_evaluate_parameter :
    evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
      (overlapEval_denominator_isUnit k a b r s hrs hr hs) (parameter k a b r s) = invT k := by
  apply (overlapEval_denominator_isUnit k a b r s hrs hr hs).mul_right_cancel
  have hx := evaluateChart_mk_mul k a b (denominator k a b r) (denominator_mem k a b r)
    (overlapEval k a b r s hrs hr hs) (overlapEval_denominator_isUnit k a b r s hrs hr hs)
    1 (coordinate W 0) (by simpa using coordinate_mem W 0)
  simp only [pow_one] at hx
  change evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
    (overlapEval_denominator_isUnit k a b r s hrs hr hs) (normalizedCoordinate k a b r 0) *
      overlapEval k a b r s hrs hr hs (denominator k a b r) =
        overlapEval k a b r s hrs hr hs (coordinate W 0) at hx
  rw [parameter, map_mul, overlap_evaluate_scalar, mul_assoc, hx,
    overlapEval_x, overlapEval_denominator]
  linear_combination -(algebraMap k O (s - r) ^ 3 * algebraMap k[X] O (q k)) * t_mul_invT k

lemma overlap_evaluate_infinity :
    evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
      (overlapEval_denominator_isUnit k a b r s hrs hr hs) =
      (Polynomial.PinchedPair.infinityOverlapRingMap k).toRingHom.comp (fromChart k a b r s hrs hr
        hs) := by
  have h : (evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
      (overlapEval_denominator_isUnit k a b r s hrs hr hs)).comp (toChart k a b r s hrs hr hs) =
      (Polynomial.PinchedPair.infinityOverlapRingMap k).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X - 1 : k[X]))
    apply Polynomial.ringHom_ext
    · intro c
      change evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
        (overlapEval_denominator_isUnit k a b r s hrs hr hs)
          (toChart k a b r s hrs hr hs (algebraMap k V c)) =
            Polynomial.PinchedPair.infinityOverlapRingMap k (algebraMap k V c)
      rw [toChart_scalar, overlap_evaluate_scalar, AlgHom.commutes]
    · change evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
        (overlapEval_denominator_isUnit k a b r s hrs hr hs)
          (toChart k a b r s hrs hr hs (standardParameter k)) =
            Polynomial.PinchedPair.infinityOverlapRingMap k (standardParameter k)
      rw [toChart_parameter, overlap_evaluate_parameter, standardParameter,
        Polynomial.PinchedPair.infinityOverlapRingMap_polynomial, Polynomial.aeval_X]
  apply RingHom.ext
  intro z
  obtain ⟨v, rfl⟩ := (ringEquiv k a b r s hrs hr hs).surjective z
  change evaluateChart k a b (denominator k a b r) (overlapEval k a b r s hrs hr hs)
      (overlapEval_denominator_isUnit k a b r s hrs hr hs) (toChart k a b r s hrs hr hs v) =
    Polynomial.PinchedPair.infinityOverlapRingMap k (fromChart k a b r s hrs hr hs
      (toChart k a b r s hrs hr hs v))
  rw [from_toChart]
  exact congrArg (fun f : V →+* O => f v) h

/-- Both permanent overlap maps agree as actual maps into the identical Proj. -/
@[reassoc] theorem overlap_compatibility :
    Scheme.PinchedLine.gluingToNode k ≫ nodeChart k a b r s hrs hr hs =
      Scheme.PinchedLine.gluingToInfinity k ≫ infinityChart k a b r s hrs hr hs := by
  have h := evaluateChart_projective_eq k a b (coordinate W 2) (denominator k a b r)
    (coordinate_mem W 2) (denominator_mem k a b r) (overlapEval k a b r s hrs hr hs)
    (by simp) (overlapEval_denominator_isUnit k a b r s hrs hr hs)
  rw [overlap_evaluate_affine, overlap_evaluate_infinity] at h
  rw [Scheme.PinchedLine.gluingToNode_spec, Scheme.PinchedLine.gluingToInfinity_spec,
    nodeChart, infinityChart, affineChart]
  change Spec.map (CommRingCat.ofHom (Polynomial.PinchedPair.affineOverlapRingMap k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr
        hs).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (fromProjectiveChart W)) ≫ chart W 2 =
    Spec.map (CommRingCat.ofHom (Polynomial.PinchedPair.infinityOverlapRingMap k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs)) ≫ projectiveChart k a b r
  change Spec.map (CommRingCat.ofHom (fromProjectiveChart W) ≫
      CommRingCat.ofHom (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs).toRingHom ≫
        CommRingCat.ofHom (Polynomial.PinchedPair.affineOverlapRingMap k).toRingHom) ≫ chart W 2 =
    Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs) ≫
      CommRingCat.ofHom (Polynomial.PinchedPair.infinityOverlapRingMap k).toRingHom) ≫
        projectiveChart k a b r at h
  simp only [Spec.map_comp, Category.assoc] at h
  exact h



include hrs in
lemma standard_z_basicOpen : PrimeSpectrum.basicOpen (zValue k r s) =
    PrimeSpectrum.basicOpen (standardParameter k) := by
  have hc : IsUnit (algebraMap k V (s - r)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (sub_ne_zero.mpr hrs.symm))).map (algebraMap k V)
  have hi : IsUnit (standardInverse k) := Localization.Away.invSelf_isUnit _
  have h : zValue k r s =
      (-(algebraMap k V (s - r)⁻¹) ^ 3 * standardInverse k) * standardParameter k ^ 3 := by
    dsimp [zValue]
    ring
  rw [h, PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_unit _ ((hc.pow 3).neg.mul hi),
    top_inf_eq,
    PrimeSpectrum.basicOpen_pow _ 3 (by decide)]

/-- The infinity-side intersection is exactly the permanent localization at w. -/
lemma infinityChart_preimage_node :
    infinityChart k a b r s hrs hr hs ⁻¹ᵁ (nodeChart k a b r s hrs hr hs).opensRange =
      PrimeSpectrum.basicOpen (standardParameter k) := by
  rw [nodeChart_range]
  change Spec.map (CommRingCat.ofHom (fromChart k a b r s hrs hr hs)) ⁻¹ᵁ
    (projectiveChart k a b r ⁻¹ᵁ Proj.basicOpen (grading W) (coordinate W 2)) = _
  rw [projectiveChart, Proj.awayι_preimage_basicOpen (grading W)
    (denominator_mem k a b r) (by decide) (coordinate_mem W 2) (by decide)]
  have h : HomogeneousLocalization.Away.isLocalizationElem
      (denominator_mem k a b r) (coordinate_mem W 2) = normalizedCoordinate k a b r 2 := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, normalizedCoordinate]
  rw [h, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (fromChart k a b r s hrs hr hs (normalizedCoordinate k a b r 2)) =
    PrimeSpectrum.basicOpen (standardParameter k)
  rw [fromChart_coordinate]
  change PrimeSpectrum.basicOpen (zValue k r s) = PrimeSpectrum.basicOpen (standardParameter k)
  exact standard_z_basicOpen k r s hrs

lemma secondCoordinate_basicOpen : PrimeSpectrum.basicOpen
  (Polynomial.PinchedPair.secondCoordinate k) =
    PrimeSpectrum.basicOpen (Polynomial.PinchedPair.conductor k) := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro p
  change Polynomial.PinchedPair.secondCoordinate k ∉ p.asIdeal ↔ Polynomial.PinchedPair.conductor
    k ∉ p.asIdeal
  apply not_congr
  have h := congrArg (Ideal.Quotient.mk p.asIdeal) (Polynomial.PinchedPair.coordinate_relation k)
  simp only [map_sub, map_mul, map_pow, map_zero] at h
  constructor
  · intro hc
    have hc' := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hc', zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_sub, neg_eq_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero h)
  · intro hq
    have hq' := Ideal.Quotient.eq_zero_iff_mem.mpr hq
    rw [hq', zero_mul, zero_pow (by decide : 3 ≠ 0), sub_zero, sub_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero h)

lemma node_denominator_coordinate :
    CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs
      (WeierstrassCurve.Projective.dehomogenize W (denominator k a b r)) =
        algebraMap k (Polynomial.PinchedPair.nodeRing k) (s - r) ^ 3 *
          Polynomial.PinchedPair.secondCoordinate k := by
  simp only [denominator, map_sub, map_mul, WeierstrassCurve.Projective.dehomogenize_coordinate,
    WeierstrassCurve.Projective.dehomogenize_constant, Matrix.cons_val_zero, Matrix.cons_val_one,
    CriticalCubic.coordinateNodeEquiv_X, CriticalCubic.coordinateNodeEquiv_Y,
    AlgEquiv.commutes, map_mul, map_pow]
  ring

/-- The node-side intersection is exactly its genuine conductor open. -/
lemma nodeChart_preimage_infinity :
    nodeChart k a b r s hrs hr hs ⁻¹ᵁ (infinityChart k a b r s hrs hr hs).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.PinchedPair.conductor k) := by
  rw [infinityChart_range]
  change Spec.map (CommRingCat.ofHom
      (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs).toRingHom) ⁻¹ᵁ
    (Spec.map (CommRingCat.ofHom (fromProjectiveChart W)) ⁻¹ᵁ
      (chart W 2 ⁻¹ᵁ Proj.basicOpen (grading W) (denominator k a b r))) = _
  rw [chart, Proj.awayι_preimage_basicOpen (grading W)
    (coordinate_mem W 2) (by decide) (denominator_mem k a b r) (by decide)]
  rw [SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen]
  have he : fromProjectiveChart W (HomogeneousLocalization.Away.isLocalizationElem
      (coordinate_mem W 2) (denominator_mem k a b r)) =
        WeierstrassCurve.Projective.dehomogenize W (denominator k a b r) := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
      fromProjectiveChart_mk W 1 (denominator k a b r) (by simpa using denominator_mem k a b r)
  change PrimeSpectrum.basicOpen (CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs
      (fromProjectiveChart W (HomogeneousLocalization.Away.isLocalizationElem
        (coordinate_mem W 2) (denominator_mem k a b r)))) =
    PrimeSpectrum.basicOpen (Polynomial.PinchedPair.conductor k)
  rw [he, node_denominator_coordinate, PrimeSpectrum.basicOpen_mul,
    PrimeSpectrum.basicOpen_unit _ (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hrs.symm)).map
      (algebraMap k (Polynomial.PinchedPair.nodeRing k))).pow 3), top_inf_eq,
        secondCoordinate_basicOpen]

lemma gluingToNode_range : (Scheme.PinchedLine.gluingToNode k).opensRange =
    PrimeSpectrum.basicOpen (Polynomial.PinchedPair.conductor k) := by
  change ((Scheme.PinchedLine.conductorOpenIso k).hom ≫ Scheme.PinchedLine.nodeOverlapInclusion
    k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Polynomial.PinchedPair.nodeOverlapRing k)
    (Polynomial.PinchedPair.conductor k)

lemma gluingToInfinity_range : (Scheme.PinchedLine.gluingToInfinity k).opensRange =
    PrimeSpectrum.basicOpen (standardParameter k) := by
  have : IsOpenImmersion (Scheme.PinchedLine.gluingToInfinity k) :=
    Scheme.PinchedLine.gluingToInfinity_open k
  let targetOpen : (Spec (.of (Polynomial.PinchedPair.infinityChartRing k))).Opens :=
    PrimeSpectrum.basicOpen (standardParameter k)
  change (Scheme.PinchedLine.gluingToInfinity k).opensRange = targetOpen
  let e : Spec (.of (Polynomial.PinchedPair.normalizationOverlapRing k)) ≅
      Spec (.of (Polynomial.PinchedPair.normalizationOverlapRing k)) :=
    Scheme.PinchedLine.reciprocalSchemeIso k
  have h₁ : (Scheme.PinchedLine.gluingToInfinity k).opensRange =
      (Scheme.PinchedLine.canonicalInfinityOpen k).opensRange :=
    Scheme.Hom.opensRange_comp_of_isIso e.hom (Scheme.PinchedLine.canonicalInfinityOpen k)
  have h₂ : (Scheme.PinchedLine.canonicalInfinityOpen k).opensRange =
      (Scheme.PinchedLine.infinityOverlapInclusion k).opensRange :=
    Scheme.Hom.opensRange_comp_of_isIso (Scheme.PinchedLine.standardOverlapSpecIso k).hom
      (Scheme.PinchedLine.infinityOverlapInclusion k)
  have h₃ : (Scheme.PinchedLine.infinityOverlapInclusion k).opensRange =
      targetOpen := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range
      (Polynomial.PinchedPair.infinityOverlapRing k)
      (algebraMap k[X] (Polynomial.PinchedPair.infinityChartRing k) Polynomial.X)
  exact h₁.trans (h₂.trans h₃)

/-- Exact applicability of the permanent infinity overlap to the actual node chart. -/
theorem infinityChart_full_overlap :
    infinityChart k a b r s hrs hr hs ⁻¹ᵁ (nodeChart k a b r s hrs hr hs).opensRange =
      (Scheme.PinchedLine.gluingToInfinity k).opensRange := by
  rw [infinityChart_preimage_node, gluingToInfinity_range]

/-- Exact applicability of the permanent conductor overlap to the actual infinity chart. -/
theorem nodeChart_full_overlap :
    nodeChart k a b r s hrs hr hs ⁻¹ᵁ (infinityChart k a b r s hrs hr hs).opensRange =
      (Scheme.PinchedLine.gluingToNode k).opensRange := by
  rw [nodeChart_preimage_infinity, gluingToNode_range]


end WeierstrassCurve.CriticalCubic.AdaptedInfinity

/- Migration source: LocalModels/CriticalCubic/InfinityCharts.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 501e5b015290a7720f339f542c3d05170a2197658757b5588686f69388599c05. -/
