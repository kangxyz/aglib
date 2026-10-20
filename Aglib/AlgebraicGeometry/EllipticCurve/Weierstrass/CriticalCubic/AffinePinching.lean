/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffineNormalization
public import Aglib.AlgebraicGeometry.Curves.Nodal.Affine
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles

/-!
# A split critical cubic as an actual affine pinching

For two distinct roots of T²+aT−b, the exact image of the original coordinate
map is the equal-evaluation subalgebra. The explicit change t=r+(s−r)u
identifies it with the zero-one pinching, preserving coordinates and both branch maps.
-/

@[expose] public noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
open scoped Polynomial
universe u

namespace WeierstrassCurve.CriticalCubic

variable (k : Type u) [Field k] (a b : k)
local notation "A" => WeierstrassCurve.Affine.CoordinateRing
  (WeierstrassCurve.toAffine (equation k a b))

lemma xPolynomial_monic : (xPolynomial k a b).Monic := by
  dsimp [xPolynomial]
  monicity!

/-- The conductor needs only one power: P*t^n is already a function on the
actual cubic. The recurrence is G_(n+2) = (x+b)*G_n - a*G_(n+1). -/
lemma coordinateMap_preimage_x_mul_pow (n : ℕ) :
    ∃ z : A, coordinateMap k a b z = xPolynomial k a b * X ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      exact ⟨WeierstrassCurve.affineX (equation k a b), by simp⟩
  | one =>
      exact ⟨WeierstrassCurve.affineY (equation k a b), by
        simp [yPolynomial, mul_comm]⟩
  | more n hn hn1 =>
      obtain ⟨z, hz⟩ := hn
      obtain ⟨w, hw⟩ := hn1
      refine ⟨(WeierstrassCurve.affineX (equation k a b) +
        algebraMap k A b) * z - algebraMap k A a * w, ?_⟩
      simp only [map_sub, map_mul, map_add, coordinateMap_X, AlgHom.commutes,
        hz, hw, algebraMap_eq]
      simp only [xPolynomial, pow_add, pow_one]
      ring

/-- Multiplication by P carries every normalization polynomial into the image
of the literal quotient-ring map; this is stronger than denominator clearing. -/
lemma coordinateMap_preimage_x_mul (p : k[X]) :
    ∃ z : A, coordinateMap k a b z = xPolynomial k a b * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨z, hz⟩ := hp
      obtain ⟨w, hw⟩ := hq
      exact ⟨z + w, by simp only [map_add, hz, hw, mul_add]⟩
  | monomial n c =>
      obtain ⟨z, hz⟩ := coordinateMap_preimage_x_mul_pow k a b n
      refine ⟨algebraMap k A c * z, ?_⟩
      simp only [map_mul, AlgHom.commutes, hz, algebraMap_eq,
        ← C_mul_X_pow_eq_monomial]
      ring

/-- Two distinct root evaluations force the remainder in monic division by P
to be constant. No algebraic closure or characteristic restriction is used. -/
lemma equal_root_values_decomposition (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0)
    (p : k[X]) (hp : p.eval r = p.eval s) :
    ∃ c : k, ∃ q : k[X], p = C c + xPolynomial k a b * q := by
  have hne : xPolynomial k a b ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    simp only [xPolynomial_natDegree, natDegree_one] at hd
    omega
  have hdeg : (p %ₘ xPolynomial k a b).natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt p (xPolynomial_monic k a b) hne
    rw [xPolynomial_natDegree] at h
    omega
  have hrem := eq_X_add_C_of_natDegree_le_one hdeg
  have hpr : p.eval r = (p %ₘ xPolynomial k a b).eval r := by
    have h := congrArg (Polynomial.eval r)
      (modByMonic_add_div p (xPolynomial k a b))
    simpa [xPolynomial, hr] using h.symm
  have hps : p.eval s = (p %ₘ xPolynomial k a b).eval s := by
    have h := congrArg (Polynomial.eval s)
      (modByMonic_add_div p (xPolynomial k a b))
    simpa [xPolynomial, hs] using h.symm
  have heval : (p %ₘ xPolynomial k a b).eval r =
      (p %ₘ xPolynomial k a b).eval s := hpr.symm.trans (hp.trans hps)
  have hlinear : (p %ₘ xPolynomial k a b).coeff 1 * (r - s) = 0 := by
    rw [hrem] at heval
    simp only [eval_add, eval_mul, eval_C, eval_X] at heval
    linear_combination heval
  have hc : (p %ₘ xPolynomial k a b).coeff 1 = 0 :=
    (mul_eq_zero.mp hlinear).resolve_right (sub_ne_zero.mpr hrs)
  have hconstant : p %ₘ xPolynomial k a b =
      C ((p %ₘ xPolynomial k a b).coeff 0) := by
    simpa only [hc, C_0, zero_mul, zero_add] using hrem
  refine ⟨(p %ₘ xPolynomial k a b).coeff 0, p /ₘ xPolynomial k a b, ?_⟩
  exact (modByMonic_add_div p (xPolynomial k a b)).symm.trans
    (congrArg (fun q : k[X] => q + xPolynomial k a b * (p /ₘ xPolynomial k a b))
      hconstant)

/-- This is only the literal subalgebra cut out by the two root evaluations,
not a replacement recognition datum or a separate geometric pinching model. -/
def rootEqualizer (r s : k) : Subalgebra k k[X] :=
  (aeval r).equalizer (aeval s)

@[simp] lemma mem_rootEqualizer (r s : k) (p : k[X]) :
    p ∈ rootEqualizer k r s ↔ p.eval r = p.eval s := Iff.rfl

lemma coordinateMap_eval_roots (r s : k)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : A) :
    (coordinateMap k a b z).eval r = (coordinateMap k a b z).eval s := by
  change ((aeval r).comp (coordinateMap k a b)) z =
    ((aeval s).comp (coordinateMap k a b)) z
  rw [(eval_coordinateMap_eq_origin_iff k a b r).mpr hr,
    (eval_coordinateMap_eq_origin_iff k a b s).mpr hs]

/-- The exact image, for the actual injective quotient normalization map. -/
lemma coordinateMap_image_iff (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (p : k[X]) :
    (∃ z : A, coordinateMap k a b z = p) ↔ p.eval r = p.eval s := by
  constructor
  · rintro ⟨z, rfl⟩
    exact coordinateMap_eval_roots k a b r s hr hs z
  · intro hp
    obtain ⟨c, q, hq⟩ := equal_root_values_decomposition k a b r s hrs hr hs p hp
    obtain ⟨z, hz⟩ := coordinateMap_preimage_x_mul k a b q
    refine ⟨algebraMap k A c + z, ?_⟩
    simpa only [map_add, AlgHom.commutes, algebraMap_eq, hz] using hq.symm

lemma coordinateMap_range_eq (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (coordinateMap k a b).range = rootEqualizer k r s := by
  ext p
  exact coordinateMap_image_iff k a b r s hrs hr hs p

/-- The actual normalization map, restricted to its proved exact image. -/
def coordinateEqualizerMap (r s : k)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    A →ₐ[k] rootEqualizer k r s :=
  (coordinateMap k a b).codRestrict (rootEqualizer k r s)
    (coordinateMap_eval_roots k a b r s hr hs)

@[simp] lemma coordinateEqualizerMap_coe (r s : k)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : A) :
    (coordinateEqualizerMap k a b r s hr hs z : k[X]) = coordinateMap k a b z := rfl

lemma coordinateEqualizerMap_bijective (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Function.Bijective (coordinateEqualizerMap k a b r s hr hs) := by
  constructor
  · intro z w h
    exact coordinateMap_injective k a b (congrArg Subtype.val h)
  · intro p
    obtain ⟨z, hz⟩ := (coordinateMap_image_iff k a b r s hrs hr hs p.val).mpr p.property
    exact ⟨z, Subtype.ext hz⟩

/-- A genuine algebra isomorphism from the original critical affine coordinate
ring. Injectivity is the permanent quotient-normalization theorem; surjectivity
is the newly proved image calculation. -/
def coordinateEqualizerEquiv (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    A ≃ₐ[k] rootEqualizer k r s :=
  AlgEquiv.ofBijective (coordinateEqualizerMap k a b r s hr hs)
    (coordinateEqualizerMap_bijective k a b r s hrs hr hs)

@[simp] lemma coordinateEqualizerEquiv_coe (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : A) :
    (coordinateEqualizerEquiv k a b r s hrs hr hs z : k[X]) =
      coordinateMap k a b z := rfl

/-- The normalization triangle commutes as actual k-algebra homomorphisms. -/
lemma coordinateEqualizerEquiv_normalization (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (rootEqualizer k r s).val.comp
      (coordinateEqualizerEquiv k a b r s hrs hr hs).toAlgHom =
        coordinateMap k a b := by
  apply AlgHom.ext
  intro z
  rfl

end WeierstrassCurve.CriticalCubic

namespace WeierstrassCurve.CriticalCubic

variable (k : Type u) [Field k]

/-- The original parameter expressed in the standard coordinate. -/
def parameterFromStandard (r s : k) : k[X] := C r + C (s - r) * X

/-- The standard parameter expressed in the original coordinate. -/
def parameterToStandard (r s : k) : k[X] := C (s - r)⁻¹ * (X - C r)

lemma parameterFromStandard_comp_toStandard (r s : k) (hrs : r ≠ s) :
    (parameterFromStandard k r s).comp (parameterToStandard k r s) = X := by
  have hd : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hc : (C (s - r) : k[X]) * C (s - r)⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hd, C_1]
  simp only [parameterFromStandard, parameterToStandard, add_comp, C_comp,
    mul_comp, X_comp]
  calc
    C r + C (s - r) * (C (s - r)⁻¹ * (X - C r)) =
        C r + (C (s - r) * C (s - r)⁻¹) * (X - C r) := by ring
    _ = X := by rw [hc]; ring

lemma parameterToStandard_comp_fromStandard (r s : k) (hrs : r ≠ s) :
    (parameterToStandard k r s).comp (parameterFromStandard k r s) = X := by
  have hd : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hc : (C (s - r)⁻¹ : k[X]) * C (s - r) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hd, C_1]
  simp only [parameterFromStandard, parameterToStandard, mul_comp, C_comp,
    sub_comp, X_comp]
  calc
    C (s - r)⁻¹ * (C r + C (s - r) * X - C r) =
        (C (s - r)⁻¹ * C (s - r)) * X := by ring
    _ = X := by rw [hc, one_mul]

/-- The explicit normalization-coordinate algebra automorphism. Its direction
is the pullback from the original t-line to the standard u-line. -/
def parameterAffineEquiv (r s : k) (hrs : r ≠ s) : k[X] ≃ₐ[k] k[X] :=
  algEquivOfCompEqX (parameterFromStandard k r s) (parameterToStandard k r s)
    (parameterFromStandard_comp_toStandard k r s hrs)
    (parameterToStandard_comp_fromStandard k r s hrs)

@[simp] lemma parameterAffineEquiv_apply (r s : k) (hrs : r ≠ s) (p : k[X]) :
    parameterAffineEquiv k r s hrs p = p.comp (parameterFromStandard k r s) := rfl

@[simp] lemma parameterAffineEquiv_symm_apply (r s : k) (hrs : r ≠ s) (p : k[X]) :
    (parameterAffineEquiv k r s hrs).symm p = p.comp (parameterToStandard k r s) := rfl

@[simp] lemma parameterAffineEquiv_X (r s : k) (hrs : r ≠ s) :
    parameterAffineEquiv k r s hrs X = parameterFromStandard k r s := by simp

@[simp] lemma parameterAffineEquiv_symm_X (r s : k) (hrs : r ≠ s) :
    (parameterAffineEquiv k r s hrs).symm X = parameterToStandard k r s := by simp

@[simp] lemma parameterAffineEquiv_eval_zero (r s : k) (hrs : r ≠ s) (p : k[X]) :
    (parameterAffineEquiv k r s hrs p).eval 0 = p.eval r := by
  simp [parameterFromStandard, eval_comp]

@[simp] lemma parameterAffineEquiv_eval_one (r s : k) (hrs : r ≠ s) (p : k[X]) :
    (parameterAffineEquiv k r s hrs p).eval 1 = p.eval s := by
  simp [parameterFromStandard, eval_comp]

@[simp] lemma parameterAffineEquiv_symm_eval_left (r s : k) (hrs : r ≠ s)
    (p : k[X]) : ((parameterAffineEquiv k r s hrs).symm p).eval r = p.eval 0 := by
  simp [parameterToStandard, eval_comp]

@[simp] lemma parameterAffineEquiv_symm_eval_right (r s : k) (hrs : r ≠ s)
    (p : k[X]) : ((parameterAffineEquiv k r s hrs).symm p).eval s = p.eval 1 := by
  simp [parameterToStandard, eval_comp, sub_ne_zero.mpr hrs.symm]

/-- Restriction of the explicit coordinate change to the literal equalizers. -/
def rootToNodeMap (r s : k) (hrs : r ≠ s) :
    rootEqualizer k r s →ₐ[k] Polynomial.PinchedPair.nodeRing k :=
  ((parameterAffineEquiv k r s hrs).toAlgHom.comp (rootEqualizer k r s).val).codRestrict
    (Polynomial.PinchedPair.nodeRing k) (by
      intro p
      change (parameterAffineEquiv k r s hrs p.val).eval 0 =
        (parameterAffineEquiv k r s hrs p.val).eval 1
      rw [parameterAffineEquiv_eval_zero, parameterAffineEquiv_eval_one]
      exact p.property)

/-- The inverse restriction uses exactly u=(t-r)/(s-r). -/
def nodeToRootMap (r s : k) (hrs : r ≠ s) :
    Polynomial.PinchedPair.nodeRing k →ₐ[k] rootEqualizer k r s :=
  ((parameterAffineEquiv k r s hrs).symm.toAlgHom.comp (Polynomial.PinchedPair.nodeRing
    k).val).codRestrict
    (rootEqualizer k r s) (by
      intro p
      change ((parameterAffineEquiv k r s hrs).symm p.val).eval r =
        ((parameterAffineEquiv k r s hrs).symm p.val).eval s
      rw [parameterAffineEquiv_symm_eval_left, parameterAffineEquiv_symm_eval_right]
      exact p.property)

/-- An actual algebra isomorphism onto permanent `Polynomial.PinchedPair.nodeRing`. -/
def rootNodeEquiv (r s : k) (hrs : r ≠ s) :
    rootEqualizer k r s ≃ₐ[k] Polynomial.PinchedPair.nodeRing k :=
  AlgEquiv.ofAlgHom (rootToNodeMap k r s hrs) (nodeToRootMap k r s hrs)
    (by
      apply AlgHom.ext
      intro p
      apply Subtype.ext
      exact (parameterAffineEquiv k r s hrs).apply_symm_apply p.val)
    (by
      apply AlgHom.ext
      intro p
      apply Subtype.ext
      exact (parameterAffineEquiv k r s hrs).symm_apply_apply p.val)

@[simp] lemma rootNodeEquiv_coe (r s : k) (hrs : r ≠ s)
    (p : rootEqualizer k r s) :
    (rootNodeEquiv k r s hrs p : k[X]) = parameterAffineEquiv k r s hrs p.val := rfl

@[simp] lemma rootNodeEquiv_symm_coe (r s : k) (hrs : r ≠ s)
    (p : Polynomial.PinchedPair.nodeRing k) :
    ((rootNodeEquiv k r s hrs).symm p : k[X]) =
      (parameterAffineEquiv k r s hrs).symm p.val := rfl

variable (a b : k)
local notation "A" => WeierstrassCurve.Affine.CoordinateRing
  (WeierstrassCurve.toAffine (equation k a b))

/-- Coefficient identities derived from the actual two roots, without dividing
by two or choosing an algebraic closure. -/
lemma coefficients_of_two_roots (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    a = -(r + s) ∧ b = -(r * s) := by
  have hp : (r - s) * (r + s + a) = 0 := by linear_combination hr - hs
  have ha : a = -(r + s) := eq_neg_of_add_eq_zero_right
    ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hrs))
  refine ⟨ha, ?_⟩
  calc
    b = r ^ 2 + a * r := (sub_eq_zero.mp hr).symm
    _ = -(r * s) := by rw [ha]; ring

lemma xPolynomial_factor_roots (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    xPolynomial k a b = (X - C r) * (X - C s) := by
  obtain ⟨ha, hb⟩ := coefficients_of_two_roots k a b r s hrs hr hs
  simp only [xPolynomial, ha, hb, map_neg, map_add, map_mul]
  ring

lemma parameterAffineEquiv_xPolynomial (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    parameterAffineEquiv k r s hrs (xPolynomial k a b) =
      C ((s - r) ^ 2) * (Polynomial.PinchedPair.conductor k : k[X]) := by
  rw [parameterAffineEquiv_apply, xPolynomial_factor_roots k a b r s hrs hr hs]
  simp only [mul_comp, sub_comp, X_comp, C_comp, parameterFromStandard,
    map_sub, map_pow]
  change (C r + (C s - C r) * X - C r) *
    (C r + (C s - C r) * X - C s) = (C s - C r) ^ 2 * (X * (X - 1))
  ring

/-- The requested algebra equivalence on the original critical affine ring. -/
def coordinateNodeEquiv (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    A ≃ₐ[k] Polynomial.PinchedPair.nodeRing k :=
  (coordinateEqualizerEquiv k a b r s hrs hr hs).trans (rootNodeEquiv k r s hrs)

/-- The map is literally the accepted normalization followed by the explicit
parameter substitution; it is not merely an abstract ring isomorphism. -/
@[simp] lemma coordinateNodeEquiv_coe (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : A) :
    (coordinateNodeEquiv k a b r s hrs hr hs z : k[X]) =
      parameterAffineEquiv k r s hrs (coordinateMap k a b z) := rfl

lemma coordinateNodeEquiv_normalization (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (Polynomial.PinchedPair.nodeRing k).val.comp (coordinateNodeEquiv k a b r s hrs hr
      hs).toAlgHom =
      (parameterAffineEquiv k r s hrs).toAlgHom.comp (coordinateMap k a b) := by
  apply AlgHom.ext
  intro z
  rfl

@[simp] lemma coordinateNodeEquiv_scalar (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (c : k) :
    coordinateNodeEquiv k a b r s hrs hr hs (algebraMap k A c) =
      algebraMap k (Polynomial.PinchedPair.nodeRing k) c :=
  (coordinateNodeEquiv k a b r s hrs hr hs).commutes c

@[simp] lemma coordinateNodeEquiv_X (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    coordinateNodeEquiv k a b r s hrs hr hs
      (WeierstrassCurve.affineX (equation k a b)) =
        algebraMap k (Polynomial.PinchedPair.nodeRing k) ((s - r) ^ 2) *
          Polynomial.PinchedPair.conductor k := by
  apply Subtype.ext
  change parameterAffineEquiv k r s hrs
    (coordinateMap k a b (WeierstrassCurve.affineX (equation k a b))) =
      C ((s - r) ^ 2) * (Polynomial.PinchedPair.conductor k : k[X])
  rw [coordinateMap_X]
  exact parameterAffineEquiv_xPolynomial k a b r s hrs hr hs

@[simp] lemma coordinateNodeEquiv_Y (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    coordinateNodeEquiv k a b r s hrs hr hs
      (WeierstrassCurve.affineY (equation k a b)) =
        algebraMap k (Polynomial.PinchedPair.nodeRing k) (r * (s - r) ^ 2) *
          Polynomial.PinchedPair.conductor k +
        algebraMap k (Polynomial.PinchedPair.nodeRing k) ((s - r) ^ 3) *
          Polynomial.PinchedPair.secondCoordinate k := by
  apply Subtype.ext
  change parameterAffineEquiv k r s hrs
    (coordinateMap k a b (WeierstrassCurve.affineY (equation k a b))) =
      C (r * (s - r) ^ 2) * (Polynomial.PinchedPair.conductor k : k[X]) +
      C ((s - r) ^ 3) * (Polynomial.PinchedPair.secondCoordinate k : k[X])
  rw [coordinateMap_Y, yPolynomial, map_mul, parameterAffineEquiv_X,
    parameterAffineEquiv_xPolynomial k a b r s hrs hr hs]
  simp only [parameterFromStandard, Polynomial.PinchedPair.conductor,
    Polynomial.PinchedPair.secondCoordinate,
    Polynomial.PinchedPair.conductorMul, map_mul, map_pow]
  ring

/-- The left standardized branch still maps to the literal original origin. -/
lemma coordinateNodeEquiv_eval_zero (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    ((aeval (0 : k)).comp (Polynomial.PinchedPair.nodeRing k).val).comp
      (coordinateNodeEquiv k a b r s hrs hr hs).toAlgHom = originMap k a b := by
  apply AlgHom.ext
  intro z
  change (coordinateNodeEquiv k a b r s hrs hr hs z : k[X]).eval 0 = originMap k a b z
  rw [coordinateNodeEquiv_coe, parameterAffineEquiv_eval_zero]
  exact congrArg (fun f : A →ₐ[k] k => f z)
    ((eval_coordinateMap_eq_origin_iff k a b r).mpr hr)

/-- The right standardized branch has the same literal origin triangle. -/
lemma coordinateNodeEquiv_eval_one (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    ((aeval (1 : k)).comp (Polynomial.PinchedPair.nodeRing k).val).comp
      (coordinateNodeEquiv k a b r s hrs hr hs).toAlgHom = originMap k a b := by
  apply AlgHom.ext
  intro z
  change (coordinateNodeEquiv k a b r s hrs hr hs z : k[X]).eval 1 = originMap k a b z
  rw [coordinateNodeEquiv_coe, parameterAffineEquiv_eval_one]
  exact congrArg (fun f : A →ₐ[k] k => f z)
    ((eval_coordinateMap_eq_origin_iff k a b s).mpr hs)

/-- The affine normalization coordinate isomorphism (standard line to original
line). Both objects are the genuine polynomial affine line. -/
def parameterAffineSchemeIso (r s : k) (hrs : r ≠ s) :
    Spec (.of k[X]) ≅ Spec (.of k[X]) :=
  Scheme.Spec.mapIso (parameterAffineEquiv k r s hrs).toRingEquiv.toCommRingCatIso.op

/-- The actual affine cubic scheme is identified with the permanent node chart. -/
def coordinateNodeSchemeIso (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Spec (.of A) ≅ Scheme.PinchedLine.nodeScheme k :=
  Scheme.Spec.mapIso (coordinateNodeEquiv k a b r s hrs hr hs).toRingEquiv.toCommRingCatIso.symm.op

/-- The actual scheme normalization square, in the variance of Spec. -/
lemma coordinateNodeSchemeIso_normalization (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Scheme.PinchedLine.normalizationMap k ≫ (coordinateNodeSchemeIso k a b r s hrs hr hs).inv =
      (parameterAffineSchemeIso k r s hrs).hom ≫ affineNormalization k a b := by
  change Spec.map (CommRingCat.ofHom (Polynomial.PinchedPair.nodeRing k).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (coordinateNodeEquiv k a b r s hrs hr hs).toRingHom) =
      Spec.map (CommRingCat.ofHom (parameterAffineEquiv k r s hrs).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coordinateMap k a b).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

lemma parameterAffineSchemeIso_branch_zero (r s : k) (hrs : r ≠ s) :
    Scheme.PinchedLine.branchMap k 0 ≫ (parameterAffineSchemeIso k r s hrs).hom =
      parameterSection k r := by
  change Spec.map (CommRingCat.ofHom (evalRingHom (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (parameterAffineEquiv k r s hrs).toRingHom) =
      Spec.map (CommRingCat.ofHom (aeval r).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact parameterAffineEquiv_eval_zero k r s hrs p

lemma parameterAffineSchemeIso_branch_one (r s : k) (hrs : r ≠ s) :
    Scheme.PinchedLine.branchMap k 1 ≫ (parameterAffineSchemeIso k r s hrs).hom =
      parameterSection k s := by
  change Spec.map (CommRingCat.ofHom (evalRingHom (1 : k))) ≫
    Spec.map (CommRingCat.ofHom (parameterAffineEquiv k r s hrs).toRingHom) =
      Spec.map (CommRingCat.ofHom (aeval s).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact parameterAffineEquiv_eval_one k r s hrs p

lemma coordinateNodeSchemeIso_origin_zero (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Scheme.PinchedLine.branchMap k 0 ≫ Scheme.PinchedLine.normalizationMap k ≫
      (coordinateNodeSchemeIso k a b r s hrs hr hs).inv = originSection k a b := by
  rw [coordinateNodeSchemeIso_normalization, ← Category.assoc,
    parameterAffineSchemeIso_branch_zero]
  exact (parameterSection_comp_eq_origin_iff k a b r).mpr hr

lemma coordinateNodeSchemeIso_origin_one (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    Scheme.PinchedLine.branchMap k 1 ≫ Scheme.PinchedLine.normalizationMap k ≫
      (coordinateNodeSchemeIso k a b r s hrs hr hs).inv = originSection k a b := by
  rw [coordinateNodeSchemeIso_normalization, ← Category.assoc,
    parameterAffineSchemeIso_branch_one]
  exact (parameterSection_comp_eq_origin_iff k a b s).mpr hs

/-- The scheme isomorphism is over the original field. -/
lemma coordinateNodeSchemeIso_over (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (coordinateNodeSchemeIso k a b r s hrs hr hs).hom ≫
      Spec.algebraMap k (Polynomial.PinchedPair.nodeRing k) = Spec.algebraMap k A := by
  exact Spec.map_algHom_algebraMap
    (coordinateNodeEquiv k a b r s hrs hr hs).symm.toAlgHom

lemma coordinateNodeSchemeIso_inv_over (r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (coordinateNodeSchemeIso k a b r s hrs hr hs).inv ≫
      Spec.algebraMap k A = Spec.algebraMap k (Polynomial.PinchedPair.nodeRing k) := by
  exact Spec.map_algHom_algebraMap (coordinateNodeEquiv k a b r s hrs hr hs).toAlgHom
end WeierstrassCurve.CriticalCubic

/- Migration source: LocalModels/CriticalCubic/AffinePinching.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 4d863c15fdb32496cb05a2eead7410b7f148819c5f79d20801be26e23ecb89f1. -/
