/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Sections
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.PoleFunctions
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.AffineComplement
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SmoothDiscriminant
public import Aglib.AlgebraicGeometry.Curves.GenericExtension
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Integrality
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SmoothLoci
public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Aglib.AlgebraicGeometry.RationalPoint.ClosedLift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# Constructing native Weierstrass coordinates

The normalization of a six-term pole relation works in every characteristic.
The resulting map has Mathlib's literal affine coordinate ring as its source.
The full construction uses the original normalized point filtration, all
positive pole spaces, the original affine complement, and the actual native
projective comparison. None of those outputs is a presentation premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped WithZero

universe u v w

namespace WeierstrassCurve.Presentation

/-- Coefficients of the relation in the ordered pole monomials
`1, x, y, x², xy, x³`. -/
structure CubicCoefficients (R : Type u) where
  /-- The constant coefficient. -/
  c0 : R
  /-- The coefficient of the original coordinate x. -/
  cx : R
  /-- The coefficient of the original coordinate y. -/
  cy : R
  /-- The coefficient of the original monomial x squared. -/
  cx2 : R
  /-- The coefficient of the original product xy. -/
  cxy : R
  /-- The coefficient of the original monomial x cubed. -/
  c3 : R

namespace CubicCoefficients

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- The actual six-term relation before normalizing its cubic coefficient. -/
def IsRelation (C : CubicCoefficients R) (x y : A) : Prop :=
  y ^ 2 = algebraMap R A C.c0 + algebraMap R A C.cx * x +
    algebraMap R A C.cy * y + algebraMap R A C.cx2 * x ^ 2 +
    algebraMap R A C.cxy * x * y + algebraMap R A C.c3 * x ^ 3

/-- Simultaneous scaling of x and y normalizes the cubic coefficient without
extracting a square or cube root and without dividing by 2 or 3. -/
def equation (C : CubicCoefficients R) : WeierstrassCurve R where
  a₁ := -C.cxy
  a₂ := C.cx2
  a₃ := -C.c3 * C.cy
  a₄ := C.c3 * C.cx
  a₆ := C.c3 ^ 2 * C.c0

/-- The original x coordinate scaled by the actual cubic coefficient. -/
def scaledX (C : CubicCoefficients R) (x : A) : A := algebraMap R A C.c3 * x
/-- The original y coordinate scaled by the same actual cubic coefficient. -/
def scaledY (C : CubicCoefficients R) (y : A) : A := algebraMap R A C.c3 * y

/-- The normalized coordinates satisfy the literal native Weierstrass equation. -/
theorem scaled_relation (C : CubicCoefficients R) (x y : A) (h : C.IsRelation x y) :
    C.scaledY y ^ 2 + algebraMap R A C.equation.a₁ * C.scaledX x * C.scaledY y +
      algebraMap R A C.equation.a₃ * C.scaledY y -
      (C.scaledX x ^ 3 + algebraMap R A C.equation.a₂ * C.scaledX x ^ 2 +
        algebraMap R A C.equation.a₄ * C.scaledX x + algebraMap R A C.equation.a₆) = 0 := by
  dsimp only [IsRelation] at h
  dsimp only [scaledX, scaledY, equation]
  simp only [map_neg, map_mul, map_pow]
  linear_combination (algebraMap R A C.c3) ^ 2 * h

/-- The actual algebra map from Mathlib's native affine Weierstrass ring. -/
def coordinateMap (C : CubicCoefficients R) (x y : A) (h : C.IsRelation x y) :
    C.equation.toAffine.CoordinateRing →ₐ[R] A :=
  WeierstrassCurve.affineLift C.equation (C.scaledX x) (C.scaledY y)
    (C.scaled_relation x y h)

@[simp] theorem coordinateMap_x (C : CubicCoefficients R) (x y : A) (h : C.IsRelation x y) :
    C.coordinateMap x y h (WeierstrassCurve.affineX C.equation) = C.scaledX x :=
  WeierstrassCurve.affineLift_x _ _ _ _

@[simp] theorem coordinateMap_y (C : CubicCoefficients R) (x y : A) (h : C.IsRelation x y) :
    C.coordinateMap x y h (WeierstrassCurve.affineY C.equation) = C.scaledY y :=
  WeierstrassCurve.affineLift_y _ _ _ _

section Field

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]

/-- Once the original x and y generate the actual target algebra, the
normalized native coordinate map is surjective. -/
theorem coordinateMap_surjective (C : CubicCoefficients k) (x y : B)
    (h : C.IsRelation x y) (hc3 : C.c3 ≠ 0)
    (hgen : Algebra.adjoin k ({x, y} : Set B) = ⊤) :
    Function.Surjective (C.coordinateMap x y h) := by
  let f := C.coordinateMap x y h
  have hs (z : B) : algebraMap k B C.c3⁻¹ * (algebraMap k B C.c3 * z) = z := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc3, map_one, one_mul]
  have hx : x ∈ f.range := by
    refine ⟨algebraMap k _ C.c3⁻¹ * WeierstrassCurve.affineX C.equation, ?_⟩
    rw [map_mul]
    change f (algebraMap k _ C.c3⁻¹) * f (WeierstrassCurve.affineX C.equation) = x
    rw [f.commutes]
    change algebraMap k B C.c3⁻¹ *
      C.coordinateMap x y h (WeierstrassCurve.affineX C.equation) = x
    rw [coordinateMap_x]
    exact hs x
  have hy : y ∈ f.range := by
    refine ⟨algebraMap k _ C.c3⁻¹ * WeierstrassCurve.affineY C.equation, ?_⟩
    rw [map_mul]
    change f (algebraMap k _ C.c3⁻¹) * f (WeierstrassCurve.affineY C.equation) = y
    rw [f.commutes]
    change algebraMap k B C.c3⁻¹ *
      C.coordinateMap x y h (WeierstrassCurve.affineY C.equation) = y
    rw [coordinateMap_y]
    exact hs y
  have hr : Algebra.adjoin k ({x, y} : Set B) ≤ f.range := by
    apply Algebra.adjoin_le
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [hgen] at hr
  intro z
  exact hr (show z ∈ (⊤ : Subalgebra k B) from trivial)

end Field
end CubicCoefficients

/-- The six monomials with candidate pole orders 0, 2, 3, 4, 5, 6. -/
def poleMonomials {A : Type v} [CommRing A] (x y : A) : Fin 6 → A :=
  ![1, x, y, x ^ 2, x * y, x ^ 3]

section BasisRelation

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

/-- Coordinates of the actual section y² in a given six-dimensional pole basis. -/
def coefficientsOfBasis (L : Submodule k A) (b : Module.Basis (Fin 6) k L)
    (y : A) (hy : y ^ 2 ∈ L) : CubicCoefficients k where
  c0 := b.repr ⟨y ^ 2, hy⟩ 0
  cx := b.repr ⟨y ^ 2, hy⟩ 1
  cy := b.repr ⟨y ^ 2, hy⟩ 2
  cx2 := b.repr ⟨y ^ 2, hy⟩ 3
  cxy := b.repr ⟨y ^ 2, hy⟩ 4
  c3 := b.repr ⟨y ^ 2, hy⟩ 5

/-- A basis of the actual pole space produces its actual six-term relation. -/
theorem coefficientsOfBasis_relation (L : Submodule k A) (b : Module.Basis (Fin 6) k L)
    (x y : A) (hy : y ^ 2 ∈ L)
    (hb : ∀ i, (b i : A) = poleMonomials x y i) :
    (coefficientsOfBasis L b y hy).IsRelation x y := by
  have H := congrArg (fun z : L => (z : A)) (b.sum_repr ⟨y ^ 2, hy⟩)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at H
  simpa [CubicCoefficients.IsRelation, coefficientsOfBasis,
    hb, poleMonomials, Algebra.smul_def, mul_assoc, add_assoc] using H.symm

end BasisRelation

section PoleValuation

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]

private theorem valuation_polynomial_at_pole_two (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k] (x : K) (hx : v x = WithZero.exp (2 : ℤ))
    (p : k[X]) (hp : p ≠ 0) :
    v (p.aeval x) = WithZero.exp (2 * (p.natDegree : ℤ)) := by
  have hpos : 1 < v x := by rw [hx, WithZero.one_lt_exp_iff]; norm_num
  rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    x hpos hp, hx, ← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

/-- Even and odd pole orders prohibit cancellation in the literal normal form. -/
theorem polynomial_normalForm_eq_zero_iff (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (p q : k[X]) : p.aeval x + q.aeval x * y = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    by_cases hp : p = 0
    · refine ⟨hp, ?_⟩
      by_contra hq
      have H : v (q.aeval x * y) = 0 := by
        simpa only [hp, map_zero, zero_add] using congrArg v h
      rw [map_mul, valuation_polynomial_at_pole_two v x hx q hq, hy] at H
      exact (mul_ne_zero WithZero.exp_ne_zero WithZero.exp_ne_zero) H
    by_cases hq : q = 0
    · have H : v (p.aeval x) = 0 := by
        simpa only [hq, map_zero, zero_mul, add_zero] using congrArg v h
      rw [valuation_polynomial_at_pole_two v x hx p hp] at H
      exact (WithZero.exp_ne_zero H).elim
    have H : v (p.aeval x) = v (q.aeval x * y) := by
      simpa only [Valuation.map_neg] using
        congrArg v (eq_neg_of_add_eq_zero_left h)
    rw [valuation_polynomial_at_pole_two v x hx p hp, map_mul,
      valuation_polynomial_at_pole_two v x hx q hq, hy, ← WithZero.exp_add] at H
    have he := WithZero.exp_inj.mp H
    omega
  · rintro ⟨rfl, rfl⟩
    simp

private theorem affineAlgHom_polynomial (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing →ₐ[k] K) (p : k[X]) :
    f (algebraMap k[X] W.toAffine.CoordinateRing p) = p.aeval (f (affineX W)) := by
  have H : f.comp (IsScalarTower.toAlgHom k k[X] W.toAffine.CoordinateRing) =
      aeval (f (affineX W)) := by
    apply Polynomial.algHom_ext
    change f (affineX W) = aeval (f (affineX W)) X
    rw [aeval_X]
  exact congrArg (fun g : k[X] →ₐ[k] K => g p) H

private theorem affineAlgHom_normalForm (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing →ₐ[k] K) (p q : k[X]) :
    f (p • (1 : W.toAffine.CoordinateRing) + q • affineY W) =
      p.aeval (f (affineX W)) + q.aeval (f (affineX W)) * f (affineY W) := by
  simp only [Algebra.smul_def, mul_one, map_add, map_mul]
  change f (algebraMap k[X] _ p) + f (algebraMap k[X] _ q) * f (affineY W) = _
  rw [affineAlgHom_polynomial W f p, affineAlgHom_polynomial W f q]

/-- The native affine Weierstrass ring injects into an actual valued field
when its coordinate images have pole values two and three. -/
theorem affineAlgHom_injective_of_pole_values (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing →ₐ[k] K) (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k]
    (hx : v (f (affineX W)) = WithZero.exp (2 : ℤ))
    (hy : v (f (affineY W)) = WithZero.exp (3 : ℤ)) : Function.Injective f := by
  intro a b hab
  have hz : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq (a - b)
  change p • (1 : W.toAffine.CoordinateRing) + q • affineY W = a - b at hpq
  have H := congrArg f hpq
  rw [affineAlgHom_normalForm, hz] at H
  obtain ⟨hp, hq⟩ := (polynomial_normalForm_eq_zero_iff v (f (affineX W))
    (f (affineY W)) hx hy p q).mp H
  apply sub_eq_zero.mp
  rw [← hpq, hp, hq, zero_smul, zero_smul, zero_add]

private theorem linearIndependent_of_distinct_pole_values
    {ι : Type*} [Finite ι] (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (s : ι → K) (d : ι → ℤ) (hd : Function.Injective d)
    (hs : ∀ i, v (s i) = WithZero.exp (d i)) : LinearIndependent k s := by
  classical
  let := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hci
  let T := Finset.univ.filter (fun j => c j ≠ 0)
  have hT : T.Nonempty := ⟨i, by simp [T, hci]⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image T d hT
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hvc (l : ι) (hcl : c l ≠ 0) : v (c l • s l) = WithZero.exp (d l) := by
    rw [Algebra.smul_def, map_mul, hv.eq_one (c l) hcl, hs l, one_mul]
  have H : v (Finset.univ.sum fun l => c l • s l) = v (c j • s j) := by
    apply v.map_sum_eq_of_lt (Finset.mem_univ j)
    intro l hl
    rw [hvc j hcj]
    by_cases hcl : c l = 0
    · simpa only [hcl, zero_smul, map_zero] using (WithZero.exp_pos (a := d j))
    · rw [hvc l hcl, WithZero.exp_lt_exp]
      have hle : d l ≤ d j := hmax l (by simp [T, hcl])
      have hlj : l ≠ j := by simpa using (Finset.mem_sdiff.mp hl).2
      exact lt_of_le_of_ne hle (fun he => hlj (hd he))
  rw [hc, map_zero, hvc j hcj] at H
  exact WithZero.exp_ne_zero H.symm

private def poleWeights : Fin 6 → ℤ := ![0, 2, 3, 4, 5, 6]

private theorem poleWeights_injective : Function.Injective poleWeights := by
  decide

/-- The original six monomials are linearly independent from their actual
pole values, in every characteristic. -/
theorem poleMonomials_linearIndependent (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ)) :
    LinearIndependent k (poleMonomials x y) := by
  apply linearIndependent_of_distinct_pole_values v (poleMonomials x y)
    poleWeights poleWeights_injective
  intro i
  fin_cases i <;>
    norm_num [poleMonomials, poleWeights, hx, hy, ← WithZero.exp_nsmul, ← WithZero.exp_add]

/-- Dimension six and actual membership turn the original monomials into
an actual basis of the displayed pole subspace. -/
def poleBasisSix (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (x y : K) (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (L : Submodule k K) (hL : Module.finrank k L = 6)
    (hm : ∀ i, poleMonomials x y i ∈ L) : Module.Basis (Fin 6) k L := by
  let b : Fin 6 → L := fun i => ⟨poleMonomials x y i, hm i⟩
  have hb : LinearIndependent k b := LinearIndependent.of_comp L.subtype
    (poleMonomials_linearIndependent v x y hx hy)
  exact basisOfLinearIndependentOfCardEqFinrank hb
    (by simpa only [Fintype.card_fin] using hL.symm)

@[simp] theorem poleBasisSix_val (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (x y : K) (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (L : Submodule k K) (hL : Module.finrank k L = 6)
    (hm : ∀ i, poleMonomials x y i ∈ L) (i : Fin 6) :
    (poleBasisSix v x y hx hy L hL hm i : K) = poleMonomials x y i := by
  simp [poleBasisSix]

/-- A genuine relation at pole order six has nonzero cubic coefficient.
Otherwise the five lower-order terms would cancel a term of order six. -/
theorem CubicCoefficients.c3_ne_zero_of_pole_values (C : CubicCoefficients k)
    (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (h : C.IsRelation x y) : C.c3 ≠ 0 := by
  intro hc3
  let m : Fin 6 → K := ![1, x, y, x ^ 2, x * y, y ^ 2]
  have hm : LinearIndependent k m := by
    apply linearIndependent_of_distinct_pole_values v m poleWeights poleWeights_injective
    intro i
    fin_cases i <;>
      norm_num [m, poleWeights, hx, hy, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  let c : Fin 6 → k := ![-C.c0, -C.cx, -C.cy, -C.cx2, -C.cxy, 1]
  dsimp only [CubicCoefficients.IsRelation] at h
  rw [hc3, map_zero, zero_mul, add_zero] at h
  have H : Finset.univ.sum (fun i => c i • m i) = 0 := by
    simp [Fin.sum_univ_succ, c, m, Algebra.smul_def]
    linear_combination h
  have hc := Fintype.linearIndependent_iff.mp hm c H (5 : Fin 6)
  norm_num [c] at hc

/-- The displayed pole functions determine all six relation coefficients uniquely. -/
theorem CubicCoefficients.eq_of_relations (C D : CubicCoefficients k)
    (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (hC : C.IsRelation x y) (hD : D.IsRelation x y) : C = D := by
  let c : Fin 6 → k :=
    ![C.c0 - D.c0, C.cx - D.cx, C.cy - D.cy,
      C.cx2 - D.cx2, C.cxy - D.cxy, C.c3 - D.c3]
  have H : Finset.univ.sum (fun i => c i • poleMonomials x y i) = 0 := by
    dsimp only [CubicCoefficients.IsRelation] at hC hD
    simp [Fin.sum_univ_succ, c, poleMonomials, Algebra.smul_def]
    linear_combination hD - hC
  have hc := Fintype.linearIndependent_iff.mp
    (poleMonomials_linearIndependent v x y hx hy) c H
  have h0 : C.c0 = D.c0 := sub_eq_zero.mp (by simpa [c] using hc (0 : Fin 6))
  have h1 : C.cx = D.cx := sub_eq_zero.mp (by simpa [c] using hc (1 : Fin 6))
  have h2 : C.cy = D.cy := sub_eq_zero.mp (by simpa [c] using hc (2 : Fin 6))
  have h3 : C.cx2 = D.cx2 := sub_eq_zero.mp (by simpa [c] using hc (3 : Fin 6))
  have h4 : C.cxy = D.cxy := sub_eq_zero.mp (by simpa [c] using hc (4 : Fin 6))
  have h5 : C.c3 = D.c3 := sub_eq_zero.mp (by simpa [c] using hc (5 : Fin 6))
  cases C
  cases D
  congr

/-- Actual six-dimensional pole data produce the unique relation and a
nonzero cubic coefficient; no polynomial relation is assumed. -/
theorem existsUnique_cubic_relation_of_pole_space (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (L : Submodule k K) (hL : Module.finrank k L = 6)
    (hm : ∀ i, poleMonomials x y i ∈ L) (hy2 : y ^ 2 ∈ L) :
    ∃! C : CubicCoefficients k, C.IsRelation x y ∧ C.c3 ≠ 0 := by
  let b := poleBasisSix v x y hx hy L hL hm
  let C := coefficientsOfBasis L b y hy2
  have hC : C.IsRelation x y := coefficientsOfBasis_relation L b x y hy2
    (poleBasisSix_val v x y hx hy L hL hm)
  refine ⟨C, ⟨hC, C.c3_ne_zero_of_pole_values v x y hx hy hC⟩, ?_⟩
  intro D hD
  exact D.eq_of_relations C v x y hx hy hD.1 hC

/-- Indices of the even powers and the odd powers times y up to a positive
pole bound. The missing pole order one is reflected in the second summand. -/
abbrev PoleBasisIndex (n : ℕ) := Fin (n / 2 + 1) ⊕ Fin ((n - 1) / 2)

private def poleBasisWeight (n : ℕ) : PoleBasisIndex n → ℤ :=
  Sum.elim (fun i => 2 * (i : ℤ)) (fun j => 2 * (j : ℤ) + 3)

private theorem poleBasisWeight_injective (n : ℕ) :
    Function.Injective (poleBasisWeight n) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      congr 1
      apply Fin.ext
      dsimp only [poleBasisWeight, Sum.elim_inl] at h
      omega
    | inr j =>
      dsimp only [poleBasisWeight, Sum.elim_inl, Sum.elim_inr] at h
      omega
  | inr i =>
    cases j with
    | inl j =>
      dsimp only [poleBasisWeight, Sum.elim_inl, Sum.elim_inr] at h
      omega
    | inr j =>
      congr 1
      apply Fin.ext
      dsimp only [poleBasisWeight, Sum.elim_inr] at h
      omega

/-- The original normal-form monomials below the given pole bound. -/
def poleBasisMonomial (x y : K) (n : ℕ) : PoleBasisIndex n → K :=
  Sum.elim (fun i => x ^ (i : ℕ)) (fun j => x ^ (j : ℕ) * y)

/-- The even and odd monomials have pairwise distinct actual pole values. -/
theorem poleBasisMonomial_linearIndependent (v : Valuation K ℤᵐ⁰)
    [hv : v.IsTrivialOn k] (x y : K)
    (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ)) (n : ℕ) :
    LinearIndependent k (poleBasisMonomial x y n) := by
  let : Fintype (PoleBasisIndex n) := inferInstanceAs (Fintype (Fin _ ⊕ Fin _))
  apply linearIndependent_of_distinct_pole_values v (poleBasisMonomial x y n)
    (poleBasisWeight n) (poleBasisWeight_injective n)
  intro i
  cases i with
  | inl i =>
    simp [poleBasisMonomial, poleBasisWeight, hx, ← WithZero.exp_nsmul, mul_comm]
  | inr j =>
    simp [poleBasisMonomial, poleBasisWeight, hx, hy, ← WithZero.exp_nsmul,
      ← WithZero.exp_add, mul_comm]

/-- For a positive bound there are exactly n original normal-form monomials. -/
theorem card_poleBasisIndex (n : ℕ) (hn : 0 < n) :
    Fintype.card (PoleBasisIndex n) = n := by
  change Fintype.card (Fin (n / 2 + 1) ⊕ Fin ((n - 1) / 2)) = n
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-- The original even and odd monomials form a basis of an actual pole space
of dimension n once their actual membership is known. -/
def poleBasis (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (x y : K) (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (n : ℕ) (hn : 0 < n) (L : Submodule k K) (hL : Module.finrank k L = n)
    (hm : ∀ i, poleBasisMonomial x y n i ∈ L) : Module.Basis (PoleBasisIndex n) k L := by
  letI : Fintype (PoleBasisIndex n) := inferInstanceAs (Fintype (Fin _ ⊕ Fin _))
  letI : Nonempty (PoleBasisIndex n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  let b : PoleBasisIndex n → L := fun i => ⟨poleBasisMonomial x y n i, hm i⟩
  have hb : LinearIndependent k b := LinearIndependent.of_comp L.subtype
    (poleBasisMonomial_linearIndependent v x y hx hy n)
  exact basisOfLinearIndependentOfCardEqFinrank hb ((card_poleBasisIndex n hn).trans hL.symm)

@[simp] theorem poleBasis_val (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (x y : K) (hx : v x = WithZero.exp (2 : ℤ)) (hy : v y = WithZero.exp (3 : ℤ))
    (n : ℕ) (hn : 0 < n) (L : Submodule k K) (hL : Module.finrank k L = n)
    (hm : ∀ i, poleBasisMonomial x y n i ∈ L) (i : PoleBasisIndex n) :
    (poleBasis v x y hx hy n hn L hL hm i : K) = poleBasisMonomial x y n i := by
  simp [poleBasis]

end PoleValuation

section CoordinateAlgebra

variable {k : Type u} [Field k] {B : Type v} {K : Type w} [CommRing B] [Field K]
  [Algebra k B] [Algebra k K]

/-- Actual generation and actual pole values give an isomorphism from the
literal native affine coordinate ring to the displayed target algebra. -/
def coordinateAlgebraEquiv (C : CubicCoefficients k) (x y : B)
    (h : C.IsRelation x y) (hc3 : C.c3 ≠ 0)
    (hgen : Algebra.adjoin k ({x, y} : Set B) = ⊤)
    (ι : B →ₐ[k] K) (v : Valuation K ℤᵐ⁰) [hv : v.IsTrivialOn k]
    (hx : v (ι x) = WithZero.exp (2 : ℤ)) (hy : v (ι y) = WithZero.exp (3 : ℤ)) :
    C.equation.toAffine.CoordinateRing ≃ₐ[k] B := by
  let f := C.coordinateMap x y h
  have hix : v ((ι.comp f) (affineX C.equation)) = WithZero.exp (2 : ℤ) := by
    change v (ι (C.coordinateMap x y h (affineX C.equation))) = _
    rw [CubicCoefficients.coordinateMap_x]
    change v (ι (algebraMap k B C.c3 * x)) = _
    rw [map_mul]
    change v (ι (algebraMap k B C.c3) * ι x) = _
    rw [ι.commutes, map_mul, hv.eq_one C.c3 hc3, hx, one_mul]
  have hiy : v ((ι.comp f) (affineY C.equation)) = WithZero.exp (3 : ℤ) := by
    change v (ι (C.coordinateMap x y h (affineY C.equation))) = _
    rw [CubicCoefficients.coordinateMap_y]
    change v (ι (algebraMap k B C.c3 * y)) = _
    rw [map_mul]
    change v (ι (algebraMap k B C.c3) * ι y) = _
    rw [ι.commutes, map_mul, hv.eq_one C.c3 hc3, hy, one_mul]
  have hfi : Function.Injective f := by
    intro a b hab
    apply affineAlgHom_injective_of_pole_values C.equation (ι.comp f) v hix hiy
    exact congrArg ι hab
  exact AlgEquiv.ofBijective f ⟨hfi, C.coordinateMap_surjective x y h hc3 hgen⟩

end CoordinateAlgebra

section OriginalSections

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k]

private theorem exists_not_mem_range_of_finrank_lt
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (hf : Function.Injective f)
    (hdim : Module.finrank k V < Module.finrank k W) :
    ∃ w : W, w ∉ LinearMap.range f := by
  classical
  by_contra h
  have hs : Function.Surjective f := by
    intro w
    by_contra hw
    exact h ⟨w, hw⟩
  exact (ne_of_lt hdim) (LinearEquiv.ofBijective f ⟨hf, hs⟩).finrank_eq

/-- The original point filtration has a genuine new section at every positive
step. This is an assertion about the actual canonical inclusion. -/
theorem exists_strict_pole_section (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) :
    ∃ s : PointDivisor.sections X hX p hp (n + 1),
      s ∉ LinearMap.range (PointDivisor.sectionsInclusion X hX p hp n) := by
  apply exists_not_mem_range_of_finrank_lt (PointDivisor.sectionsInclusion X hX p hp n)
    (PointDivisor.sectionsInclusion_injective X hX p hp n)
  rw [PointDivisor.sections_finrank X hX p hp hg n hn,
    PointDivisor.sections_finrank X hX p hp hg (n + 1) (by omega)]
  omega

/-- An actual original section in O(2p) outside the canonical O(p) image. -/
def xSection (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : PointDivisor.sections X hX p hp 2 :=
  (exists_strict_pole_section X hX p hp hg 1 (by omega)).choose

theorem xSection_not_mem_range (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    xSection X hX p hp hg ∉ LinearMap.range (PointDivisor.sectionsInclusion X hX p hp 1) :=
  (exists_strict_pole_section X hX p hp hg 1 (by omega)).choose_spec

/-- An actual original section in O(3p) outside the canonical O(2p) image. -/
def ySection (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : PointDivisor.sections X hX p hp 3 :=
  (exists_strict_pole_section X hX p hp hg 2 (by omega)).choose

theorem ySection_not_mem_range (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ySection X hX p hp hg ∉ LinearMap.range (PointDivisor.sectionsInclusion X hX p hp 2) :=
  (exists_strict_pole_section X hX p hp hg 2 (by omega)).choose_spec

end OriginalSections
section ProjectiveClosure

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.Projective

variable {k : Type u} [Field k]

/-- An actual affine Weierstrass chart of a smooth proper integral curve
extends to an isomorphism with the literal projective cubic. The original
open-chart comparison and structural map are retained. -/
theorem exists_projectiveOverIso_of_affineIso
    (X : FScheme k) [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    (W : WeierstrassCurve k)
    (e : Over.mk (U.ι ≫ X.hom) ≅ affineOver W) :
    ∃ E : X ≅ curveOver W,
      U.ι ≫ E.hom.left = e.hom.left ≫ affineChart W := by
  let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral (scheme W) := scheme_isIntegral_of_isDomain W
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have heOver : e.hom.left ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) = U.ι ≫ X.hom := e.hom.w
  let g := Scheme.genericToOpen U hU ≫ e.hom.left ≫ affineChart W
  have hg : g ≫ structureMap W = X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
    dsimp only [g]
    rw [Category.assoc, Category.assoc, affineChart_structure, heOver,
      ← Category.assoc, Scheme.genericToOpen_ι]
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  obtain ⟨f, hf, hfg⟩ := normalProperCurveGenericExtension k X.left (scheme W)
    X.hom (structureMap W) inferInstance inferInstance
    (Scheme.smoothFieldNormality k X.left X.hom inferInstance) inferInstance g hg
  have hlocal : U.ι ≫ f = e.hom.left ≫ affineChart W := by
    have : IsDominant (Scheme.genericToOpen U hU ≫ U.ι) := by
      rw [Scheme.genericToOpen_ι]
      infer_instance
    let : IsDominant (Scheme.genericToOpen U hU) :=
      IsDominant.of_comp_of_isOpenImmersion (Scheme.genericToOpen U hU) U.ι
    apply ext_of_isDominant_of_isSeparated (structureMap W) ?_
      (Scheme.genericToOpen U hU) ?_
    · rw [Category.assoc, hf, Category.assoc, affineChart_structure, heOver]
    · rw [← Category.assoc, Scheme.genericToOpen_ι, hfg]
  let : IsOpenImmersion (U.ι ≫ f) := hlocal.symm ▸ inferInstance
  let : IsDominant (U.ι ≫ f) := Scheme.isDominant_of_isOpenImmersion (U.ι ≫ f)
  let : IsDominant U.ι := Scheme.isDominant_of_isOpenImmersion U.ι
  let : IsDominant f := IsDominant.of_comp U.ι f
  have : IsProper (f ≫ structureMap W) := hf.symm ▸ inferInstance
  let : IsProper f := IsProper.of_comp f (structureMap W)
  have hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
    let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap U.ι)) :=
      Scheme.FunctionField.fieldMap_isIso U.ι
    have : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f) ≫
        CommRingCat.ofHom (Scheme.functionFieldMap U.ι)) := by
      change IsIso (CommRingCat.ofHom
        ((Scheme.functionFieldMap U.ι).comp (Scheme.functionFieldMap f)))
      rw [← Scheme.functionFieldMap_comp]
      exact Scheme.FunctionField.fieldMap_isIso (U.ι ≫ f)
    exact IsIso.of_isIso_comp_right
      (CommRingCat.ofHom (Scheme.functionFieldMap f))
      (CommRingCat.ofHom (Scheme.functionFieldMap U.ι))
  let A := (affineChart W).opensRange
  let s : A.toScheme ⟶ X.left := (affineChart W).isoOpensRange.inv ≫ e.inv.left ≫ U.ι
  let : IsOpenImmersion s := by dsimp only [s]; infer_instance
  let : IsIntegral A.toScheme := IsIntegral.of_isIso (affineChart W).isoOpensRange.hom
  let : IsDominant s := Scheme.isDominant_of_isOpenImmersion s
  have hs : s ≫ f = A.ι := by
    dsimp only [s]
    rw [Category.assoc, Category.assoc, hlocal, ← Category.assoc e.inv.left]
    have he : e.inv.left ≫ e.hom.left = 𝟙 _ := by
      simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.inv_hom_id
    rw [he, Category.id_comp, (affineChart W).isoOpensRange_inv_comp]
  have hAff : IsIso (f ∣_ A) := Scheme.isIso_restrict_of_dominant_section f A s hs
  let r : Scheme.RationalPoint k (scheme W) :=
    ⟨structureMap W, infinitySection W, infinitySection_structure W⟩
  have hclosed : IsClosed ({infinityPoint W} : Set (scheme W)) := r.point_isClosed
  let a := infinitySmoothSection W (IsLocalRing.closedPoint k)
  have ha : infinitySmoothChart W a = infinityPoint W :=
    congrArg (fun h : Spec (.of k) ⟶ scheme W => h (IsLocalRing.closedPoint k))
      (infinitySmoothSection_chart W)
  have hdvr := Scheme.smoothChart_closedPoint_dvr (infinitySmoothChart W)
    (structureMap W) a (ha.symm ▸ hclosed)
  let : IsDiscreteValuationRing ((scheme W).presheaf.stalk (infinityPoint W)) := ha ▸ hdvr
  obtain ⟨V, hinf, hV⟩ :=
    Scheme.exists_isIso_restrict_of_isProper_birational_at_valuationRing f hff (infinityPoint W)
  let : IsIso f := by
    apply (MorphismProperty.isomorphisms.iff f).mp
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := MorphismProperty.isomorphisms Scheme)
    intro y
    by_cases hy : y = infinityPoint W
    · exact ⟨V, hy ▸ hinf, (MorphismProperty.isomorphisms.iff _).mpr hV⟩
    · have hyA : y ∈ A := by
        change y ∈ Set.range (affineChart W)
        rw [affineChart_range_complement]
        exact hy
      exact ⟨A, hyA, (MorphismProperty.isomorphisms.iff _).mpr hAff⟩
  exact ⟨Over.isoMk (asIso f) hf, hlocal⟩

/-- If the original rational point is outside that original affine chart,
the resulting literal projective isomorphism sends its actual section map
to the native infinity section over the same field. -/
theorem exists_pointedOverIso_of_affineIso
    (X : FScheme k) [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (hpU : p default ∉ U)
    (W : WeierstrassCurve k)
    (e : Over.mk (U.ι ≫ X.hom) ≅ affineOver W) :
    ∃ E : X ≅ curveOver W, p ≫ E.hom.left = infinitySection W ∧
      U.ι ≫ E.hom.left = e.hom.left ≫ affineChart W := by
  obtain ⟨E, hE⟩ := exists_projectiveOverIso_of_affineIso X U hU W e
  let : IsIso E.hom.left := inferInstanceAs (IsIso ((Over.forget _).map E.hom))
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hpoint : E.hom.left (p default) = infinityPoint W := by
    by_contra hne
    have hm : E.hom.left (p default) ∈ Set.range (affineChart W) := by
      rw [affineChart_range_complement]
      exact hne
    obtain ⟨a, ha⟩ := hm
    obtain ⟨u, hu⟩ := e.hom.left.homeomorph.surjective a
    have H := congrArg (fun f : U.toScheme ⟶ scheme W => f u) hE
    change E.hom.left (U.ι u) = affineChart W (e.hom.left u) at H
    have hu' : (show U.toScheme ⟶ Spec (.of (affineRing W)) from e.hom.left) u = a := hu
    have H' : E.hom.left (U.ι u) = E.hom.left (p default) :=
      H.trans ((congrArg (affineChart W) hu').trans ha)
    have he : U.ι u = p default := E.hom.left.homeomorph.injective H'
    exact hpU (he ▸ u.property)
  have hEOver : E.hom.left ≫ structureMap W = X.hom := E.hom.w
  refine ⟨E, ?_, hE⟩
  apply Scheme.RationalPoint.rationalPoint_eq_of_apply_eq k (structureMap W)
  · rw [Category.assoc, hEOver]
    exact hp
  · exact infinitySection_structure W
  · change E.hom.left (p default) = infinitySection W default
    exact hpoint.trans (congrArg (infinitySection W) (Subsingleton.elim _ _))

end ProjectiveClosure

section OriginalPoleFunctions

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)

variable [IsIntegral X.left] [IsNoetherian X.left]
  [∀ q : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk q.val)]

/-- The original structural field action on the curve function field. -/
local instance instAlgebraFunctionFieldForPoleSpaces : Algebra k X.left.functionField :=
  Scheme.functionFieldConstantsAlgebra X.left X.hom

/-- The pole subspace is the range of the original normalized section map,
with the original structural field action. -/
def poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) : Submodule k X.left.functionField :=
  (PointDivisor.sectionsToFunctionField X hX p hp hg n).range

theorem mem_poleSpace_iff (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (z : X.left.functionField) :
    z ∈ poleSpace X hX p hp hg n ↔
      DivisorClass.IsFractionalSection X.left (PointDivisor.pointDivisor X p hp n) ⊤ z :=
  PointDivisor.mem_range_sectionsToFunctionField_iff X hX p hp hg n z

theorem poleSpace_finrank (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) :
    Module.finrank k (poleSpace X hX p hp hg n) = n := by
  rw [poleSpace, LinearMap.finrank_range_of_inj
    (PointDivisor.sectionsToFunctionField_injective X hX p hp hg n)]
  exact PointDivisor.sections_finrank X hX p hp hg n hn

theorem poleSpace_mono (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) {m n : ℕ} (hmn : m ≤ n) :
    poleSpace X hX p hp hg m ≤ poleSpace X hX p hp hg n := by
  classical
  intro z hz
  rw [mem_poleSpace_iff] at hz ⊢
  rcases hz with rfl | hz
  · exact Or.inl rfl
  right
  intro q hq
  have H := hz q hq
  by_cases h : q = PointDivisor.closedPoint X p hp
  · simp only [PointDivisor.pointDivisor, h, Finsupp.single_eq_same] at H ⊢
    omega
  · simpa only [PointDivisor.pointDivisor, Finsupp.single_eq_of_ne h] using H

theorem one_mem_poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    (1 : X.left.functionField) ∈ poleSpace X hX p hp hg n := by
  rw [mem_poleSpace_iff]
  right
  intro q _
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, by trivial⟩⟩
  have H : X.left.ord (1 : X.left.functionField) q.val = 0 := by
    simpa only [map_one] using
      (Scheme.ord_of_isUnit (X := X.left) (U := ⊤) (f := 1) isUnit_one
        (show q.val ∈ (⊤ : X.left.Opens) from trivial))
  rw [H, zero_add]
  exact PointDivisor.pointDivisor_nonneg X p hp n q

theorem mul_mem_poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) {m n : ℕ} {z t : X.left.functionField}
    (hz : z ∈ poleSpace X hX p hp hg m) (ht : t ∈ poleSpace X hX p hp hg n) :
    z * t ∈ poleSpace X hX p hp hg (m + n) := by
  rw [mem_poleSpace_iff] at hz ht ⊢
  simpa only [PointDivisor.pointDivisor, Nat.cast_add, Finsupp.single_add] using
    DivisorClass.isFractionalSection_mul X.left hz ht

theorem pow_mem_poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) {m : ℕ} {z : X.left.functionField}
    (hz : z ∈ poleSpace X hX p hp hg m) (n : ℕ) :
    z ^ n ∈ poleSpace X hX p hp hg (n * m) := by
  induction n with
  | zero => simpa only [pow_zero, zero_mul] using one_mem_poleSpace X hX p hp hg 0
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using mul_mem_poleSpace X hX p hp hg ih hz

private theorem strict_section_not_mem_previous
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ)
    (s : PointDivisor.sections X hX p hp (n + 1))
    (hs : s ∉ LinearMap.range (PointDivisor.sectionsInclusion X hX p hp n)) :
    PointDivisor.sectionsToFunctionField X hX p hp hg (n + 1) s ∉
      poleSpace X hX p hp hg n := by
  rintro ⟨t, ht⟩
  apply hs
  refine ⟨t, (PointDivisor.sectionsToFunctionField_injective X hX p hp hg (n + 1)) ?_⟩
  exact (PointDivisor.sectionsFractionalEquiv_inclusion_value X hX p hp hg n t).trans ht

/-- Strictness in the original inclusion filtration forces the exact
original pole order, rather than merely an upper bound. -/
theorem strict_section_order (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ)
    (s : PointDivisor.sections X hX p hp (n + 1))
    (hs : s ∉ LinearMap.range (PointDivisor.sectionsInclusion X hX p hp n)) :
    X.left.ord (PointDivisor.sectionsToFunctionField X hX p hp hg (n + 1) s)
      (PointDivisor.closedPoint X p hp).val = -((n : ℤ) + 1) := by
  classical
  let z := PointDivisor.sectionsToFunctionField X hX p hp hg (n + 1) s
  have hnot : z ∉ poleSpace X hX p hp hg n := strict_section_not_mem_previous X hX p hp hg n s hs
  have hz0 : z ≠ 0 := by intro he; exact hnot (he.symm ▸ (poleSpace X hX p hp hg n).zero_mem)
  have hz : z ∈ poleSpace X hX p hp hg (n + 1) := LinearMap.mem_range_self _ s
  have H := ((mem_poleSpace_iff X hX p hp hg (n + 1) z).mp hz).resolve_left hz0
  have hlo := H (PointDivisor.closedPoint X p hp) (by trivial)
  simp only [PointDivisor.pointDivisor, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one] at hlo
  have hprev : ¬ 0 ≤ X.left.ord z (PointDivisor.closedPoint X p hp).val + (n : ℤ) := by
    intro h
    apply hnot
    rw [mem_poleSpace_iff]
    right
    intro q hq
    by_cases he : q = PointDivisor.closedPoint X p hp
    · simpa only [PointDivisor.pointDivisor, he, Finsupp.single_eq_same] using h
    · simpa only [PointDivisor.pointDivisor, Finsupp.single_eq_of_ne he] using H q hq
  dsimp only [z] at hlo hprev
  omega

/-- The actual rational function of the chosen original O(2p) section. -/
def xFunction (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : X.left.functionField :=
  PointDivisor.sectionsToFunctionField X hX p hp hg 2 (xSection X hX p hp hg)

/-- The actual rational function of the chosen original O(3p) section. -/
def yFunction (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : X.left.functionField :=
  PointDivisor.sectionsToFunctionField X hX p hp hg 3 (ySection X hX p hp hg)

theorem xFunction_order (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    X.left.ord (xFunction X hX p hp hg) (PointDivisor.closedPoint X p hp).val = -2 :=
  strict_section_order X hX p hp hg 1 (xSection X hX p hp hg) (xSection_not_mem_range X hX p hp hg)

theorem yFunction_order (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    X.left.ord (yFunction X hX p hp hg) (PointDivisor.closedPoint X p hp).val = -3 :=
  strict_section_order X hX p hp hg 2 (ySection X hX p hp hg) (ySection_not_mem_range X hX p hp hg)

/-- The native valuation at the original point, with its smooth-curve
witness supplied by the original properties. -/
def originalPoleValuation (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Valuation X.left.functionField ℤᵐ⁰ := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  exact PointDivisor.poleValuation X (PointDivisor.closedPoint X p hp)

instance originalPoleValuation_trivial
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (originalPoleValuation X hX p hp).IsTrivialOn k := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  change (PointDivisor.poleValuation X (PointDivisor.closedPoint X p hp)).IsTrivialOn k
  infer_instance

omit [∀ q : Scheme.ClosedPoint X.left,
    IsDiscreteValuationRing (X.left.presheaf.stalk q.val)] in
private theorem poleValue_of_order_eq [SmoothOfRelativeDimension 1 X.hom]
    (q : Scheme.ClosedPoint X.left)
    (z : X.left.functionField) (n : ℤ) (hn : 0 < n) (hz : X.left.ord z q.val = -n) :
    PointDivisor.poleValuation X q z = WithZero.exp n := by
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, Scheme.ord_zero, Pi.zero_apply] at hz
    omega
  have hq : Order.coheight q.val = 1 := by
    by_contra h
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hz
    omega
  rw [PointDivisor.poleValuation_eq_exp_neg_order X q hq z hz0, hz, neg_neg]

theorem xFunction_poleValue (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    originalPoleValuation X hX p hp
      (xFunction X hX p hp hg) = WithZero.exp (2 : ℤ) := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  exact poleValue_of_order_eq X _ _ 2 (by norm_num) (xFunction_order X hX p hp hg)

theorem yFunction_poleValue (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    originalPoleValuation X hX p hp
      (yFunction X hX p hp hg) = WithZero.exp (3 : ℤ) := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  exact poleValue_of_order_eq X _ _ 3 (by norm_num) (yFunction_order X hX p hp hg)

theorem xFunction_mem_poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : xFunction X hX p hp hg ∈ poleSpace X hX p hp hg 2 :=
  LinearMap.mem_range_self _ _

theorem yFunction_mem_poleSpace (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) : yFunction X hX p hp hg ∈ poleSpace X hX p hp hg 3 :=
  LinearMap.mem_range_self _ _

/-- Every actual pole section is regular on the original punctured open. -/
theorem poleSpace_regularAway (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) {n : ℕ} {z : X.left.functionField}
    (hz : z ∈ poleSpace X hX p hp hg n) :
    letI : SmoothOfRelativeDimension 1 X.hom := hX.smooth
    PointDivisor.RegularAway X (PointDivisor.closedPoint X p hp) z := by
  classical
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let U := PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)
  let : Nonempty U := ⟨⟨genericPoint X.left, PointDivisor.genericPoint_mem_complementOpen X _⟩⟩
  have hnonneg : ∀ q : Scheme.ClosedPoint X.left, q.val ∈ U → 0 ≤ X.left.ord z q.val := by
    intro q hq
    rcases (mem_poleSpace_iff X hX p hp hg n z).mp hz with rfl | hz
    · simp
    have he : q ≠ PointDivisor.closedPoint X p hp := by
      intro he
      change q.val ≠ (PointDivisor.closedPoint X p hp).val at hq
      exact hq (congrArg (fun q : Scheme.ClosedPoint X.left => q.val) he)
    simpa only [PointDivisor.pointDivisor, Finsupp.single_eq_of_ne he, add_zero] using
      hz q (by trivial)
  exact Divisors.exists_section_of_nonneg_orders X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le U z hnonneg

include hX in
/-- The original chosen x function makes the original marked-point
complement affine; no affine-model or projective-presentation premise is used. -/
theorem original_complement_isAffine (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    IsAffineOpen (PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)) := by
  let : IsProper X.hom := hX.proper
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  obtain ⟨f, hf, hfg, hfin, hdom, hpre, hAff⟩ :=
    PointDivisor.exists_finite_pencil_with_affine_complement X (PointDivisor.closedPoint X p hp)
      (xFunction X hX p hp hg)
      (by rw [xFunction_order]; norm_num)
      (poleSpace_regularAway X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg))
  exact hAff

/-- Every normal-form monomial lies in the actual original pole space for
its displayed bound. This uses multiplication of actual rational functions. -/
theorem originalPoleMonomial_mem (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (i : PoleBasisIndex n) :
    poleBasisMonomial (xFunction X hX p hp hg) (yFunction X hX p hp hg) n i ∈
      poleSpace X hX p hp hg n := by
  cases i with
  | inl i =>
    exact poleSpace_mono X hX p hp hg (show (i : ℕ) * 2 ≤ n by omega)
      (pow_mem_poleSpace X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg) i)
  | inr j =>
    exact poleSpace_mono X hX p hp hg (show (j : ℕ) * 2 + 3 ≤ n by omega)
      (mul_mem_poleSpace X hX p hp hg
        (pow_mem_poleSpace X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg) j)
        (yFunction_mem_poleSpace X hX p hp hg))

/-- An actual basis of every positive original pole space by the original
x-powers and x-powers times y. -/
def originalPoleBasis (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) :
    Module.Basis (PoleBasisIndex n) k (poleSpace X hX p hp hg n) :=
  poleBasis (originalPoleValuation X hX p hp)
    (xFunction X hX p hp hg) (yFunction X hX p hp hg)
    (xFunction_poleValue X hX p hp hg) (yFunction_poleValue X hX p hp hg)
    n hn (poleSpace X hX p hp hg n) (poleSpace_finrank X hX p hp hg n hn)
    (originalPoleMonomial_mem X hX p hp hg n)

@[simp] theorem originalPoleBasis_val
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (hn : 0 < n) (i : PoleBasisIndex n) :
    (originalPoleBasis X hX p hp hg n hn i : X.left.functionField) =
      poleBasisMonomial (xFunction X hX p hp hg) (yFunction X hX p hp hg) n i := by
  simp [originalPoleBasis]

private theorem originalSixMonomials_mem
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (i : Fin 6) :
    poleMonomials (xFunction X hX p hp hg) (yFunction X hX p hp hg) i ∈
      poleSpace X hX p hp hg 6 := by
  fin_cases i
  · exact one_mem_poleSpace X hX p hp hg 6
  · exact poleSpace_mono X hX p hp hg (by norm_num : 2 ≤ 6)
      (xFunction_mem_poleSpace X hX p hp hg)
  · exact poleSpace_mono X hX p hp hg (by norm_num : 3 ≤ 6)
      (yFunction_mem_poleSpace X hX p hp hg)
  · exact poleSpace_mono X hX p hp hg (by norm_num : 2 * 2 ≤ 6)
      (pow_mem_poleSpace X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg) 2)
  · exact poleSpace_mono X hX p hp hg (by norm_num : 2 + 3 ≤ 6)
      (mul_mem_poleSpace X hX p hp hg
        (xFunction_mem_poleSpace X hX p hp hg) (yFunction_mem_poleSpace X hX p hp hg))
  · exact pow_mem_poleSpace X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg) 3

/-- The original pointed genus-one curve produces its unique six-term
relation with nonzero cubic coefficient, in every characteristic. -/
theorem existsUnique_original_cubic_relation
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ∃! C : CubicCoefficients k,
      C.IsRelation (xFunction X hX p hp hg) (yFunction X hX p hp hg) ∧ C.c3 ≠ 0 :=
  existsUnique_cubic_relation_of_pole_space
    (originalPoleValuation X hX p hp)
    (xFunction X hX p hp hg) (yFunction X hX p hp hg)
    (xFunction_poleValue X hX p hp hg) (yFunction_poleValue X hX p hp hg)
    (poleSpace X hX p hp hg 6) (poleSpace_finrank X hX p hp hg 6 (by norm_num))
    (originalSixMonomials_mem X hX p hp hg)
    (pow_mem_poleSpace X hX p hp hg (yFunction_mem_poleSpace X hX p hp hg) 2)

omit [AlgebraicGeometry.IsNoetherian X.left] [∀ q : Scheme.ClosedPoint X.left,
    IsDiscreteValuationRing (X.left.presheaf.stalk q.val)] in
include hX in
theorem original_complement_nonempty (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    ((PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)) :
      Set X.left).Nonempty := by
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  exact ⟨genericPoint X.left, PointDivisor.genericPoint_mem_complementOpen X _⟩

/-- The original structural field action on sections of the original point complement. -/
local instance puncturedSectionsAlgebra (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Algebra k Γ(X.left, PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)) :=
  (Scheme.constantSection X _).toAlgebra

/-- The original generic-germ map on the original punctured curve. -/
def puncturedValue (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Γ(X.left, PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)) →ₐ[k]
      X.left.functionField :=
  PointDivisor.openSectionValue X _ (original_complement_nonempty X hX p hp)

omit [AlgebraicGeometry.IsNoetherian X.left] [∀ q : Scheme.ClosedPoint X.left,
    IsDiscreteValuationRing (X.left.presheaf.stalk q.val)] in
theorem puncturedValue_injective
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Function.Injective (puncturedValue X hX p hp) :=
  PointDivisor.openSectionValue_injective X _ (original_complement_nonempty X hX p hp)

/-- Every regular section of the actual complement has a finite original
pole bound at the removed point. -/
theorem puncturedValue_mem_some_poleSpace
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1)
    (s : Γ(X.left, PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp))) :
    ∃ n : ℕ, 0 < n ∧ puncturedValue X hX p hp s ∈ poleSpace X hX p hp hg n := by
  classical
  let z := puncturedValue X hX p hp s
  let n := (-X.left.ord z (PointDivisor.closedPoint X p hp).val).toNat + 1
  refine ⟨n, by omega, ?_⟩
  rw [mem_poleSpace_iff]
  right
  intro q _
  by_cases he : q = PointDivisor.closedPoint X p hp
  · simp only [PointDivisor.pointDivisor, he, Finsupp.single_eq_same]
    change 0 ≤ X.left.ord z (PointDivisor.closedPoint X p hp).val + (n : ℤ)
    dsimp only [n]
    omega
  · simp only [PointDivisor.pointDivisor, Finsupp.single_eq_of_ne he, add_zero]
    apply PointDivisor.openSectionValue_order_nonneg X _
      (original_complement_nonempty X hX p hp) s q.val
    change q.val ≠ (PointDivisor.closedPoint X p hp).val
    exact fun h => he (Subtype.ext h)

/-- Sections with the original x and y generic values generate the actual
coordinate algebra of the original punctured curve. The proof uses every
original pole space, rather than a generation premise. -/
theorem puncturedSections_adjoin_eq_top
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1)
    (x y : Γ(X.left, PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)))
    (hx : puncturedValue X hX p hp x = xFunction X hX p hp hg)
    (hy : puncturedValue X hX p hp y = yFunction X hX p hp hg) :
    Algebra.adjoin k ({x, y} : Set Γ(X.left,
      PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp))) = ⊤ := by
  classical
  let S := Algebra.adjoin k ({x, y} : Set Γ(X.left,
    PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)))
  let ι := puncturedValue X hX p hp
  let T := S.map ι
  have hxS : x ∈ S := Algebra.subset_adjoin (by simp)
  have hyS : y ∈ S := Algebra.subset_adjoin (by simp)
  apply top_unique
  intro s _
  obtain ⟨n, hn, hs⟩ := puncturedValue_mem_some_poleSpace X hX p hp hg s
  let L := poleSpace X hX p hp hg n
  let b := originalPoleBasis X hX p hp hg n hn
  have hm (i : PoleBasisIndex n) : (b i : X.left.functionField) ∈ T := by
    change (originalPoleBasis X hX p hp hg n hn i : X.left.functionField) ∈ T
    rw [originalPoleBasis_val]
    cases i with
    | inl i =>
      refine ⟨x ^ (i : ℕ), S.pow_mem hxS _, ?_⟩
      change ι (x ^ (i : ℕ)) = xFunction X hX p hp hg ^ (i : ℕ)
      rw [map_pow, hx]
    | inr j =>
      refine ⟨x ^ (j : ℕ) * y, S.mul_mem (S.pow_mem hxS _) hyS, ?_⟩
      change ι (x ^ (j : ℕ) * y) =
        xFunction X hX p hp hg ^ (j : ℕ) * yFunction X hX p hp hg
      rw [map_mul, map_pow, hx, hy]
  have H := congrArg L.subtype (b.sum_repr ⟨ι s, hs⟩)
  rw [map_sum] at H
  simp only [map_smul] at H
  have hsum : (Finset.univ.sum fun i => b.repr ⟨ι s, hs⟩ i • (b i : X.left.functionField))
      ∈ T := T.toSubmodule.sum_mem (fun i _ => T.toSubmodule.smul_mem _ (hm i))
  have ht : ι s ∈ T := H ▸ hsum
  obtain ⟨t, ht, hts⟩ := ht
  have he : t = s := puncturedValue_injective X hX p hp hts
  exact he ▸ ht

include hX in
/-- The actual affine coordinate algebra of the original punctured curve is
isomorphic to a literal native Weierstrass coordinate ring. -/
theorem exists_original_coordinateAlgebraEquiv
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ∃ W : WeierstrassCurve k, Nonempty (W.toAffine.CoordinateRing ≃ₐ[k]
      Γ(X.left, PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp))) := by
  obtain ⟨x, hx⟩ := poleSpace_regularAway X hX p hp hg (xFunction_mem_poleSpace X hX p hp hg)
  obtain ⟨y, hy⟩ := poleSpace_regularAway X hX p hp hg (yFunction_mem_poleSpace X hX p hp hg)
  have hx' : puncturedValue X hX p hp x = xFunction X hX p hp hg := hx
  have hy' : puncturedValue X hX p hp y = yFunction X hX p hp hg := hy
  obtain ⟨C, hC, _⟩ := existsUnique_original_cubic_relation X hX p hp hg
  have hxy : C.IsRelation x y := by
    dsimp only [CubicCoefficients.IsRelation] at hC ⊢
    apply puncturedValue_injective X hX p hp
    simpa only [map_pow, map_add, map_mul, AlgHom.commutes, hx', hy'] using hC.1
  refine ⟨C.equation, ⟨coordinateAlgebraEquiv C x y hxy hC.2
    (puncturedSections_adjoin_eq_top X hX p hp hg x y hx' hy')
    (puncturedValue X hX p hp)
    (originalPoleValuation X hX p hp) ?_ ?_⟩⟩
  · rw [hx']
    exact xFunction_poleValue X hX p hp hg
  · rw [hy']
    exact yFunction_poleValue X hX p hp hg

end OriginalPoleFunctions

section FinalPresentation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k]

/-- Every original smooth proper genus-one curve with an original rational
point has a pointed presentation by the literal native Weierstrass cubic
over that same field. No group, Picard representation or presentation is
assumed, and no characteristic restriction is imposed. -/
theorem exists_pointed_weierstrassPresentation
    (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ∃ W : WeierstrassCurve k, ∃ E : X ≅ WeierstrassCurve.Projective.curveOver W,
      p ≫ E.hom.left = WeierstrassCurve.Projective.infinitySection W := by
  let : IsIntegral X.left := PointDivisor.isIntegral_of_properties X hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : ∀ q : Scheme.ClosedPoint X.left,
      IsDiscreteValuationRing (X.left.presheaf.stalk q.val) :=
    PointDivisor.isDiscreteValuationRing_stalk X hX
  let : Algebra k X.left.functionField := Scheme.functionFieldConstantsAlgebra X.left X.hom
  let U := PointDivisor.complementOpen X.left (PointDivisor.closedPoint X p hp)
  let : Algebra k Γ(X.left, U) := (Scheme.constantSection X U).toAlgebra
  have hU := original_complement_isAffine X hX p hp hg
  obtain ⟨W, ⟨e⟩⟩ := exists_original_coordinateAlgebraEquiv X hX p hp hg
  let eAff : U.toScheme ≅ Spec (.of W.toAffine.CoordinateRing) :=
    hU.isoSpec ≪≫ Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  have heAff : eAff.hom ≫ (WeierstrassCurve.Projective.affineOver W).hom = U.ι ≫ X.hom := by
    change (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing)) = _
    rw [Category.assoc, ← Spec.map_comp]
    have hscalar : CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing) ≫
        CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom (Scheme.constantSection X U) := by
      ext a
      exact e.commutes a
    rw [hscalar]
    exact PointDivisor.openToSpecΓ_constants X U
  let : IsProper X.hom := hX.proper
  obtain ⟨E, hpoint, _⟩ := exists_pointedOverIso_of_affineIso X U
    (original_complement_nonempty X hX p hp) p hp (by
      change p default ≠ (PointDivisor.closedPoint X p hp).val → False
      intro h
      apply h
      rw [PointDivisor.closedPoint_val]
      exact congrArg p (Subsingleton.elim _ _)) W (Over.isoMk eAff heAff)
  exact ⟨W, E, hpoint⟩

/-- The literal discriminant is nonzero as a proved consequence of the
constructed original pointed isomorphism. -/
theorem exists_nonsingular_pointed_weierstrassPresentation
    (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ∃ W : WeierstrassCurve k, W.Δ ≠ 0 ∧
      ∃ E : X ≅ WeierstrassCurve.Projective.curveOver W,
        p ≫ E.hom.left = WeierstrassCurve.Projective.infinitySection W := by
  obtain ⟨W, E, hpoint⟩ := exists_pointed_weierstrassPresentation X hX p hp hg
  let : Smooth X.hom := curveProperties_smooth hX
  let : IsIso E.inv.left := inferInstanceAs (IsIso ((Over.forget _).map E.inv))
  have he : E.inv.left ≫ X.hom = WeierstrassCurve.Projective.structureMap W := E.inv.w
  have hW : Smooth (WeierstrassCurve.Projective.structureMap W) := by
    rw [← he]
    infer_instance
  exact ⟨W, WeierstrassCurve.Projective.discriminant_ne_zero_of_smooth W hW, E, hpoint⟩

end FinalPresentation

end WeierstrassCurve.Presentation
