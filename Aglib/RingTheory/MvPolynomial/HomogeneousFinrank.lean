/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinatePieces
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The number of monomials of a given degree

* `Finsupp.finite_degree_eq`: the monomials `a : σ →₀ ℕ` of degree `m` in finitely many variables
  form a finite type (`Finsupp.finite_of_degree_eq`).
* `Finsupp.natCard_degree_eq`: there are `(|σ| + m - 1).choose m` of them (stars and bars,
  `Sym.card_sym_eq_choose`).
* `MvPolynomial.finrank_homogeneousSubmodule_eq`: over a field, the homogeneous polynomials of
  degree `m` have this dimension, through the monomial basis `homogeneousPieceBasis`.
* `MvPolynomial.homogeneousSubmoduleEquivFinFun`: `R[x]_m ≃ₗ[R] R^N` for `N` the number of
  monomials of degree `m`.
-/

@[expose] public section

noncomputable section

universe u

namespace Finsupp

/-- The monomials of a given degree in finitely many variables form a finite type. -/
instance finite_degree_eq (σ : Type*) [Finite σ] (m : ℕ) :
    Finite {a : σ →₀ ℕ // a.degree = m} :=
  (Finsupp.finite_of_degree_eq m).to_subtype

/-- **Stars and bars**: there are `(#σ + m - 1).choose m` monomials of degree `m` in the
variables `σ`. -/
theorem natCard_degree_eq (σ : Type*) [Fintype σ] (m : ℕ) :
    Nat.card {a : σ →₀ ℕ // a.degree = m} = (Fintype.card σ + m - 1).choose m := by
  classical
  rw [← Nat.card_congr ((Sym.equivNatSum σ m).trans
    (Equiv.subtypeEquivRight (q := fun a : σ →₀ ℕ => a.degree = m) fun _ => Iff.rfl)),
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]

end Finsupp

namespace MvPolynomial

/-- **The dimension of the homogeneous polynomials of degree `m`** over a field: there are
`C(|σ| + m - 1, m)` monomials of degree `m` in `|σ|` variables. -/
theorem finrank_homogeneousSubmodule_eq (σ : Type*) [Fintype σ] (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K m) = (Fintype.card σ + m - 1).choose m := by
  rw [Module.finrank_eq_nat_card_basis (homogeneousPieceBasis (ι := σ) K m),
    Finsupp.natCard_degree_eq]

/-- **The monomial basis**: `R[x]_m ≃ₗ[R] R^N` for `N` the number of monomials of degree `m`. -/
def homogeneousSubmoduleEquivFinFun (σ : Type u) [Finite σ] (R : Type u) [CommRing R] (m : ℕ)
    {N : ℕ} (hN : Nat.card {a : σ →₀ ℕ // a.degree = m} = N) :
    homogeneousSubmodule σ R m ≃ₗ[R] (Fin N → R) :=
  (homogeneousPieceBasis (ι := σ) R m).equivFun.trans
    (LinearEquiv.funCongrLeft R R (Finite.equivFinOfCardEq hN).symm)

end MvPolynomial
