/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Grading
public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Homogeneous Rees localization and the actual saturated affine chart

Evaluation at t=1 maps the actual homogeneous localization of `reesAlgebra I`
at a*t into A[1/a]. The literal localization zero criterion proves injectivity,
and ideal-power induction identifies its image with the existing canonical
`Localization.Away.saturatedChart A I a`.

The resulting A-algebra equivalence preserves the original degree-zero scalar
map and the actual b/a and homogeneous-fraction formulas. All arguments work
over arbitrary commutative rings and ideals, including zero/unit ideals and
zero or nilpotent a. No domain, Noetherian or nontriviality premise is used.

This is the ring comparison needed by actual Proj charts. It does not construct
a geometric blowup, its Cartier universal property, global gluing, properness
or flat base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open Polynomial
universe u
namespace reesAlgebra
variable {A : Type u} [CommRing A]

/-- The homogeneous degree-one Rees element `aX` associated to an element of the ideal. -/
def degreeOne (I : Ideal A) (a : I) : reesAlgebra I :=
  homogeneous I 1 ⟨a, by simpa only [pow_one] using a.property⟩

lemma degreeOne_mem (I : Ideal A) (a : I) : degreeOne I a ∈ grading I 1 :=
  (homogeneous I 1 ⟨a, by simpa only [pow_one] using a.property⟩).property

@[simp] lemma degreeOne_val (I : Ideal A) (a : I) :
    (degreeOne I a : A[X]) = monomial 1 (a : A) := rfl

/-- The homogeneous localization of the Rees algebra away from the degree-one element `aX`. -/
abbrev homogeneousAway (I : Ideal A) (a : I) :=
  HomogeneousLocalization.Away (grading I) (degreeOne I a)

/-- The Rees-algebra map obtained by evaluating the polynomial variable at one in `A[1/a]`. -/
def evalAtOne (I : Ideal A) (a : I) : reesAlgebra I →ₐ[A] Localization.Away (a : A) :=
  (Polynomial.aeval (1 : Localization.Away (a : A))).comp (reesAlgebra I).val

@[simp] lemma evalAtOne_degreeOne (I : Ideal A) (a : I) :
    evalAtOne I a (degreeOne I a) = algebraMap A (Localization.Away (a : A)) a := by
  simp [evalAtOne, degreeOne, homogeneous]

lemma evalAtOne_degreeOne_isUnit (I : Ideal A) (a : I) :
    IsUnit (evalAtOne I a (degreeOne I a)) := by
  rw [evalAtOne_degreeOne]
  exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : A)) (a : A)

/-- The extension of evaluation at one to the localization of the Rees algebra at `aX`. -/
def localizedEvaluation (I : Ideal A) (a : I) :
    Localization.Away (degreeOne I a) →ₐ[A] Localization.Away (a : A) :=
  IsLocalization.Away.liftAlgHom (degreeOne I a) (f := evalAtOne I a)
    (evalAtOne_degreeOne_isUnit I a)

/-- The ring map from homogeneous Rees localization to `A[1/a]` induced by evaluation at one. -/
def awayEvaluation (I : Ideal A) (a : I) :
    homogeneousAway I a →+* Localization.Away (a : A) :=
  (localizedEvaluation I a).toRingHom.comp
    (algebraMap (homogeneousAway I a) (Localization.Away (degreeOne I a)))

lemma evalAtOne_of_mem (I : Ideal A) (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ grading I n) :
    evalAtOne I a p = algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) := by
  change aeval (1 : Localization.Away (a : A)) (p : A[X]) = _
  rw [eq_monomial_coeff hp]
  simp

lemma awayEvaluation_mk (I : Ideal A) (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ grading I (n • 1)) :
    awayEvaluation I a
        (HomogeneousLocalization.Away.mk (grading I) (degreeOne_mem I a) n p hp) =
      algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) *
        IsLocalization.Away.invSelf (a : A) ^ n := by
  change IsLocalization.Away.lift (degreeOne I a) (evalAtOne_degreeOne_isUnit I a)
    (HomogeneousLocalization.Away.mk (grading I) (degreeOne_mem I a) n p hp).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  have hp' : p ∈ grading I n := by simpa only [smul_eq_mul, mul_one] using hp
  change evalAtOne I a p = evalAtOne I a (degreeOne I a ^ n) * _
  rw [evalAtOne_of_mem I a n p hp', map_pow, evalAtOne_degreeOne]
  have hu := IsLocalization.Away.mul_invSelf (S := Localization.Away (a : A)) (a : A)
  calc
    _ = algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) *
        (algebraMap A (Localization.Away (a : A)) (a : A) *
          IsLocalization.Away.invSelf (a : A)) ^ n := by rw [hu, one_pow, mul_one]
    _ = _ := by ring

lemma awayEvaluation_injective (I : Ideal A) (a : I) :
    Function.Injective (awayEvaluation I a) := by
  suffices hzero : ∀ z : homogeneousAway I a, awayEvaluation I a z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  intro z hz
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading I) (degreeOne_mem I a) z
  have hp' : p ∈ grading I n := by simpa only [smul_eq_mul, mul_one] using hp
  have heval : algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) = 0 := by
    have h := congrArg (fun w : Localization.Away (a : A) =>
      w * algebraMap A (Localization.Away (a : A)) (a : A) ^ n) hz
    rw [awayEvaluation_mk] at h
    have hc :
        (algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) *
            IsLocalization.Away.invSelf (a : A) ^ n) *
          algebraMap A (Localization.Away (a : A)) (a : A) ^ n =
        algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) := by
      calc
        _ = algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) *
            (algebraMap A (Localization.Away (a : A)) (a : A) *
              IsLocalization.Away.invSelf (a : A)) ^ n := by ring
        _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rw [hc, zero_mul] at h
    exact h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (a : A))
    (Localization.Away (a : A)) ((p : A[X]).coeff n)).mp heval
  obtain ⟨k, hk⟩ := s.property
  change (s : A) * (p : A[X]).coeff n = 0 at hs
  rw [← hk] at hs
  have hr : degreeOne I a ^ k * p = 0 := by
    apply Subtype.ext
    change (degreeOne I a : A[X]) ^ k * (p : A[X]) = 0
    rw [degreeOne_val, eq_monomial_coeff hp', monomial_pow, one_mul,
      monomial_mul_monomial, hs, map_zero]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨degreeOne I a ^ k, ⟨k, rfl⟩⟩, hr⟩

lemma fraction_pow_mem (I : Ideal A) (a : I) (n : ℕ) (b : A) (hb : b ∈ I ^ n) :
    algebraMap A (Localization.Away (a : A)) b *
        IsLocalization.Away.invSelf (a : A) ^ n ∈
      Localization.Away.saturatedChart A I (a : A) := by
  induction n generalizing b with
  | zero =>
      simpa only [pow_zero, mul_one] using
        (Localization.Away.saturatedChart A I (a : A)).algebraMap_mem b
  | succ n ih =>
      rw [pow_succ'] at hb
      refine Submodule.smul_induction_on hb ?_ ?_
      · intro x hx y hy
        change algebraMap A (Localization.Away (a : A)) (x * y) *
            IsLocalization.Away.invSelf (a : A) ^ (n + 1) ∈ _
        have heq : algebraMap A (Localization.Away (a : A)) (x * y) *
              IsLocalization.Away.invSelf (a : A) ^ (n + 1) =
            Localization.Away.fraction (a : A) x *
              (algebraMap A (Localization.Away (a : A)) y *
                IsLocalization.Away.invSelf (a : A) ^ n) := by
          rw [map_mul]
          dsimp only [Localization.Away.fraction]
          ring
        rw [heq]
        exact (Localization.Away.saturatedChart A I (a : A)).mul_mem
          (Localization.Away.fraction_mem I (a : A) x hx) (ih y hy)
      · intro x y hx hy
        change algebraMap A (Localization.Away (a : A)) (x + y) *
            IsLocalization.Away.invSelf (a : A) ^ (n + 1) ∈ _
        rw [map_add, add_mul]
        exact (Localization.Away.saturatedChart A I (a : A)).add_mem hx hy

lemma awayEvaluation_mem (I : Ideal A) (a : I) (z : homogeneousAway I a) :
    awayEvaluation I a z ∈ Localization.Away.saturatedChart A I (a : A) := by
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading I) (degreeOne_mem I a) z
  rw [awayEvaluation_mk]
  exact fraction_pow_mem I a n _ (p.property n)

lemma awayEvaluation_base (I : Ideal A) (a : I) (r : A) :
    awayEvaluation I a
        (HomogeneousLocalization.fromZeroRingHom (grading I)
          (Submonoid.powers (degreeOne I a)) ((degreeZeroEquiv I).symm r)) =
      algebraMap A (Localization.Away (a : A)) r := by
  change localizedEvaluation I a
    (Localization.mk ((degreeZeroEquiv I).symm r : reesAlgebra I) 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  change IsLocalization.Away.lift (degreeOne I a) (evalAtOne_degreeOne_isUnit I a)
    (algebraMap (reesAlgebra I) (Localization.Away (degreeOne I a))
      ((degreeZeroEquiv I).symm r)) = _
  rw [IsLocalization.Away.lift_eq, degreeZeroEquiv_symm_coe]
  exact (evalAtOne I a).commutes r

instance (I : Ideal A) (a : I) : Algebra A (homogeneousAway I a) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading I) (Submonoid.powers (degreeOne I a))).comp
    (degreeZeroEquiv I).symm.toRingHom).toAlgebra

/-- The algebra map from homogeneous Rees localization to `A[1/a]` induced by evaluation at one. -/
def awayAlgHom (I : Ideal A) (a : I) :
    homogeneousAway I a →ₐ[A] Localization.Away (a : A) where
  __ := awayEvaluation I a
  commutes' r := awayEvaluation_base I a r

lemma awayAlgHom_range (I : Ideal A) (a : I) :
    (awayAlgHom I a).range = Localization.Away.saturatedChart A I (a : A) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    exact awayEvaluation_mem I a w
  · change Algebra.adjoin A {z | ∃ b ∈ I,
        z = algebraMap A (Localization.Away (a : A)) b *
          IsLocalization.Away.invSelf (a : A)} ≤ (awayAlgHom I a).range
    apply Algebra.adjoin_le
    rintro z ⟨b, hb, rfl⟩
    let b' : I := ⟨b, hb⟩
    refine ⟨HomogeneousLocalization.Away.mk (grading I) (degreeOne_mem I a) 1
      (degreeOne I b') (by simpa only [one_smul] using degreeOne_mem I b'), ?_⟩
    change awayEvaluation I a _ = _
    rw [awayEvaluation_mk]
    simp only [degreeOne_val, coeff_monomial, ite_true, pow_one, b']

/-- The actual homogeneous localization is the actual saturated affine chart. -/
def awayEquiv (I : Ideal A) (a : I) :
    homogeneousAway I a ≃ₐ[A] Localization.Away.saturatedChart A I (a : A) :=
  (AlgEquiv.ofInjective (awayAlgHom I a) (awayEvaluation_injective I a)).trans
    (Subalgebra.equivOfEq _ _ (awayAlgHom_range I a))

@[simp] lemma awayEquiv_apply (I : Ideal A) (a : I) (z : homogeneousAway I a) :
    (awayEquiv I a z : Localization.Away (a : A)) = awayEvaluation I a z := rfl

lemma awayEquiv_base (I : Ideal A) (a : I) (r : A) :
    awayEquiv I a
        (HomogeneousLocalization.fromZeroRingHom (grading I)
          (Submonoid.powers (degreeOne I a)) ((degreeZeroEquiv I).symm r)) =
      algebraMap A (Localization.Away.saturatedChart A I (a : A)) r := by
  apply Subtype.ext
  rw [awayEquiv_apply]
  exact awayEvaluation_base I a r

lemma awayEquiv_mk (I : Ideal A) (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ grading I (n • 1)) :
    (awayEquiv I a
        (HomogeneousLocalization.Away.mk (grading I) (degreeOne_mem I a) n p hp) :
      Localization.Away (a : A)) =
      algebraMap A (Localization.Away (a : A)) ((p : A[X]).coeff n) *
        IsLocalization.Away.invSelf (a : A) ^ n :=
  awayEvaluation_mk I a n p hp

lemma awayEquiv_ratio (I : Ideal A) (a b : I) :
    (awayEquiv I a
        (HomogeneousLocalization.Away.mk (grading I) (degreeOne_mem I a) 1
          (degreeOne I b) (by simpa only [one_smul] using degreeOne_mem I b)) :
      Localization.Away (a : A)) = Localization.Away.fraction (a : A) (b : A) := by
  rw [awayEquiv_apply]
  change awayEvaluation I a _ =
    algebraMap A (Localization.Away (a : A)) (b : A) * IsLocalization.Away.invSelf (a : A)
  simpa only [degreeOne_val, coeff_monomial, ite_true, pow_one] using
    awayEvaluation_mk I a 1 (degreeOne I b)
      (by simpa only [one_smul] using degreeOne_mem I b)

end reesAlgebra
