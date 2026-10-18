/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Evaluation of homogeneous polynomials

Scaling every variable by the same element multiplies the evaluation of a degree-`n`
homogeneous polynomial by the `n`th power of that element. The coefficient homomorphism is
arbitrary, and no finiteness of the variable type or invertibility of the scaling factor is needed.

Over a field, the degree-`m` homogeneous polynomials in finitely many variables `σ` have
dimension at most `(m + 1)^{|σ|}` (`MvPolynomial.finrank_homogeneousSubmodule_le`): they are
spanned by the monomials of degree `m`, and such a monomial is determined by its exponents, which
lie in `{0, …, m}`.
-/

@[expose] public section

namespace MvPolynomial.IsHomogeneous

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]
  {p : MvPolynomial ι R} {n : ℕ}

/-- Homogeneous evaluation commutes with a common multiplicative scaling of all variables. -/
theorem eval₂_mul (hp : p.IsHomogeneous n) (f : R →+* S) (v : ι → S) (c : S) :
    p.eval₂ f (fun i => c * v i) = c ^ n * p.eval₂ f v := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [eval₂_add, ihp, ihq, mul_add]
  | monomial d r hd =>
    have hdeg : d.degree = n := by
      simpa [Finsupp.degree_eq_weight_one, ← Pi.one_def] using hd
    simp only [eval₂_monomial, mul_pow, Finsupp.prod_mul]
    have hc : d.prod (fun _ k => c ^ k) = c ^ n := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
    rw [hc]
    ac_rfl

end MvPolynomial.IsHomogeneous

namespace MvPolynomial

/-- The degree-`m` homogeneous polynomials in finitely many variables `σ` over a field have
dimension at most `(m + 1)^{|σ|}`. -/
theorem finrank_homogeneousSubmodule_le (σ : Type*) [Fintype σ] (K : Type*) [Field K]
    (m : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K m) ≤ (m + 1) ^ Fintype.card σ := by
  classical
  let f : {d : σ →₀ ℕ | d.degree = m} → (σ → Fin (m + 1)) := fun d i =>
    ⟨d.1 i, Nat.lt_succ_of_le ((Finsupp.le_degree i d.1).trans_eq d.2)⟩
  have hf : Function.Injective f := by
    intro d d' h
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  have : Finite {d : σ →₀ ℕ | d.degree = m} := Finite.of_injective f hf
  let := Fintype.ofFinite {d : σ →₀ ℕ | d.degree = m}
  rw [homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = m}).finrank_eq, Module.finrank_finsupp_self]
  calc Fintype.card {d : σ →₀ ℕ | d.degree = m} ≤ Fintype.card (σ → Fin (m + 1)) :=
        Fintype.card_le_of_injective f hf
    _ = (m + 1) ^ Fintype.card σ := by simp

end MvPolynomial
