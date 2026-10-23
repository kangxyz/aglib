/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Linear coordinate maps on coefficients

Taking coordinates in a field basis is linear, not multiplicative. The existing
additive coefficient map preserves homogeneity and commutes with evaluation at
points over the scalar field. No ring-homomorphism assumption on coordinates is used.
-/

@[expose] public section

namespace MvPolynomial

/-- Additive maps on coefficients preserve the degree of a homogeneous polynomial. -/
theorem IsHomogeneous.map_addHom {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (f : R →+ S) :
    MvPolynomial.IsHomogeneous (AddMonoidAlgebra.map f p : MvPolynomial σ S) d := by
  intro m hm
  apply hp
  intro hz
  simp [hz] at hm

/-- A linear coordinate map commutes with evaluation at scalar-field points. -/
theorem eval_map_linearMap {K R S σ : Type*} [CommSemiring K]
    [CommSemiring R] [CommSemiring S] [Algebra K R] [Algebra K S]
    (f : R →ₗ[K] S) (p : MvPolynomial σ R) (x : σ → K) :
    eval (fun i => algebraMap K S (x i)) (AddMonoidAlgebra.map f.toAddMonoidHom p) =
      f (eval (fun i => algebraMap K R (x i)) p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [AddMonoidAlgebra.map_add, map_add, hp, hq]
  | monomial m r =>
    rw [show AddMonoidAlgebra.map f.toAddMonoidHom (monomial m r) =
      monomial m (f r) from AddMonoidAlgebra.map_single _ _ _, eval_monomial,
      eval_monomial]
    have hR : m.prod (fun i e => algebraMap K R (x i) ^ e) =
        algebraMap K R (m.prod (fun i e => x i ^ e)) := by
      simp [Finsupp.prod, map_prod, map_pow]
    have hS : m.prod (fun i e => algebraMap K S (x i) ^ e) =
        algebraMap K S (m.prod (fun i e => x i ^ e)) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [hR, hS, mul_comm r, ← Algebra.smul_def, f.map_smul, Algebra.smul_def, mul_comm]

end MvPolynomial
