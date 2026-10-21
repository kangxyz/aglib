/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.RingTheory.Norm.Basic

/-!
# Intrinsic small-degree coordinates of an affine Weierstrass cubic

The dimension of a principal-ideal quotient is invariant under actual algebra
isomorphisms. Mathlib computes it as the degree of the quadratic algebra norm,
whose two summands have distinct parity. This gives the degree-two and
degree-three coordinate spaces over every field, without a pole-order input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate
universe u

namespace WeierstrassCurve.Projective

variable {k : Type u} [Field k]

private lemma normalForm_eq (W : WeierstrassCurve k) (p q : k[X]) :
    p • (1 : W.toAffine.CoordinateRing) + q • affineY W =
      algebraMap k[X] W.toAffine.CoordinateRing p +
        algebraMap k[X] W.toAffine.CoordinateRing q * affineY W := by
  simp only [Algebra.smul_def, mul_one]

/-- The principal-ideal colength of a nonzero coordinate-ring element is the
native polynomial norm degree. -/
theorem affineColength_eq_normDegree (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing) (hf : f ≠ 0) :
    Module.finrank k (W.toAffine.CoordinateRing ⧸ Ideal.span {f}) =
      (Algebra.norm k[X] f).natDegree :=
  finrank_quotient_span_eq_natDegree_norm (Affine.CoordinateRing.basis W.toAffine) hf

/-- Actual algebra equivalences preserve the small-degree filtration, by
transporting the actual principal ideal and its quotient. -/
theorem affineAlgEquiv_normDegree (W V : WeierstrassCurve k)
    (e : W.toAffine.CoordinateRing ≃ₐ[k] V.toAffine.CoordinateRing)
    (f : W.toAffine.CoordinateRing) (hf : f ≠ 0) :
    (Algebra.norm k[X] (e f)).natDegree = (Algebra.norm k[X] f).natDegree := by
  rw [← affineColength_eq_normDegree V (e f) (by simpa only [map_zero] using e.injective.ne hf),
    ← affineColength_eq_normDegree W f hf]
  exact (Ideal.quotientEquivAlg (Ideal.span {f}) (Ideal.span {e f}) e
    (by simp [Ideal.map_span, Set.image_singleton])).toLinearEquiv.finrank_eq.symm

private lemma degree_bounds (W : WeierstrassCurve k) (p q : k[X]) (n : ℕ)
    (h : (Algebra.norm k[X]
      (p • (1 : W.toAffine.CoordinateRing) + q • affineY W)).natDegree ≤ n) :
    (p ≠ 0 → 2 * p.natDegree ≤ n) ∧
      (q ≠ 0 → 2 * q.natDegree + 3 ≤ n) := by
  have hd := degree_le_of_natDegree_le h
  change (Algebra.norm k[X] (p • (1 : W.toAffine.CoordinateRing) +
    q • Affine.CoordinateRing.mk W.toAffine Y)).degree ≤ (n : WithBot ℕ) at hd
  rw [Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine)] at hd
  obtain ⟨hp, hq⟩ := max_le_iff.mp hd
  constructor
  · intro hp0
    rw [degree_eq_natDegree hp0] at hp
    simp only [Nat.cast_withBot, ← WithBot.coe_nsmul, WithBot.coe_le_coe] at hp
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using! hp
  · intro hq0
    rw [degree_eq_natDegree hq0] at hq
    simp only [Nat.cast_withBot, ← WithBot.coe_nsmul, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe] at hq
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using! hq

/-- Colength at most two forces the usual linear x-coordinate form. -/
theorem affine_normalForm_of_normDegree_le_two (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing) (h : (Algebra.norm k[X] f).natDegree ≤ 2) :
    ∃ a r : k, f = algebraMap k _ a * affineX W + algebraMap k _ r := by
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq f
  change p • (1 : W.toAffine.CoordinateRing) + q • affineY W = f at hpq
  have hb := degree_bounds W p q 2 (by simpa only [hpq] using h)
  have hq : q = 0 := by
    by_contra hq
    have := hb.2 hq
    omega
  have hp : p.natDegree ≤ 1 := by
    by_cases hp : p = 0
    · simp [hp]
    · have := hb.1 hp
      omega
  refine ⟨p.coeff 1, p.coeff 0, ?_⟩
  rw [← hpq, hq, zero_smul, add_zero]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp, Algebra.smul_def, mul_one]
  simp only [map_add, map_mul, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply k k[X], affineX]

/-- Colength at most three forces the usual linear y-coordinate form. -/
theorem affine_normalForm_of_normDegree_le_three (W : WeierstrassCurve k)
    (f : W.toAffine.CoordinateRing) (h : (Algebra.norm k[X] f).natDegree ≤ 3) :
    ∃ b s t : k, f = algebraMap k _ b * affineY W +
      algebraMap k _ s * affineX W + algebraMap k _ t := by
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq f
  change p • (1 : W.toAffine.CoordinateRing) + q • affineY W = f at hpq
  have hb := degree_bounds W p q 3 (by simpa only [hpq] using h)
  have hp : p.natDegree ≤ 1 := by
    by_cases hp : p = 0
    · simp [hp]
    · have := hb.1 hp
      omega
  have hq : q.natDegree = 0 := by
    by_cases hq : q = 0
    · simp [hq]
    · have := hb.2 hq
      omega
  refine ⟨q.coeff 0, p.coeff 1, p.coeff 0, ?_⟩
  rw [← hpq]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp, eq_C_of_natDegree_eq_zero hq,
    normalForm_eq]
  simp only [map_add, map_mul, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply k k[X], affineX]
  ring

/-- The x-coordinate has intrinsic degree two. -/
theorem affineX_normDegree (W : WeierstrassCurve k) :
    (Algebra.norm k[X] (affineX W)).natDegree = 2 := by
  have hx : (X : k[X]) • (1 : W.toAffine.CoordinateRing) +
      (0 : k[X]) • affineY W = affineX W := by simp [Algebra.smul_def, affineX]
  apply natDegree_eq_of_degree_eq_some
  rw [← hx]
  change (Algebra.norm k[X] ((X : k[X]) • (1 : W.toAffine.CoordinateRing) +
    (0 : k[X]) • Affine.CoordinateRing.mk W.toAffine Y)).degree = (2 : WithBot ℕ)
  rw [Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine)]
  norm_num

/-- The y-coordinate has intrinsic degree three. -/
theorem affineY_normDegree (W : WeierstrassCurve k) :
    (Algebra.norm k[X] (affineY W)).natDegree = 3 := by
  have hy : (0 : k[X]) • (1 : W.toAffine.CoordinateRing) +
      (1 : k[X]) • affineY W = affineY W := by simp
  apply natDegree_eq_of_degree_eq_some
  rw [← hy]
  change (Algebra.norm k[X] ((0 : k[X]) • (1 : W.toAffine.CoordinateRing) +
    (1 : k[X]) • Affine.CoordinateRing.mk W.toAffine Y)).degree = (3 : WithBot ℕ)
  rw [Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine)]
  norm_num

private lemma affineX_ne_zero (W : WeierstrassCurve k) : affineX W ≠ 0 := by
  intro hx
  have h := affineX_normDegree W
  have hz : Algebra.norm k[X] (0 : W.toAffine.CoordinateRing) = 0 :=
    (Algebra.norm_eq_zero_iff_of_basis (Affine.CoordinateRing.basis W.toAffine)).mpr rfl
  rw [hx, hz, natDegree_zero] at h
  omega

private lemma affineY_ne_zero (W : WeierstrassCurve k) : affineY W ≠ 0 := by
  intro hy
  have h := affineY_normDegree W
  have hz : Algebra.norm k[X] (0 : W.toAffine.CoordinateRing) = 0 :=
    (Algebra.norm_eq_zero_iff_of_basis (Affine.CoordinateRing.basis W.toAffine)).mpr rfl
  rw [hy, hz, natDegree_zero] at h
  omega

/-- Both images of the actual coordinates under an affine algebra isomorphism
have the standard triangular form. The leading coefficients are treated next. -/
theorem affineAlgEquiv_coordinateForms (W V : WeierstrassCurve k)
    (e : W.toAffine.CoordinateRing ≃ₐ[k] V.toAffine.CoordinateRing) :
    (∃ a r : k, e (affineX W) =
      algebraMap k _ a * affineX V + algebraMap k _ r) ∧
    (∃ b s t : k, e (affineY W) = algebraMap k _ b * affineY V +
      algebraMap k _ s * affineX V + algebraMap k _ t) := by
  constructor
  · apply affine_normalForm_of_normDegree_le_two
    rw [affineAlgEquiv_normDegree W V e _ (affineX_ne_zero W), affineX_normDegree]
  · apply affine_normalForm_of_normDegree_le_three
    rw [affineAlgEquiv_normDegree W V e _ (affineY_ne_zero W), affineY_normDegree]

end WeierstrassCurve.Projective
