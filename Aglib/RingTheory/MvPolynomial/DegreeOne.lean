/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Original coordinates as a basis of the degree-one homogeneous module

The actual degree-one homogeneous polynomial submodule has the original
variables as its basis. Its coordinates are the native coefficients at
`Finsupp.single i 1`. Degree-one exponent vectors are canonically the
coordinate indices. Coefficient and index universes are independent; the
coordinate type is arbitrary, and the coefficient ring may be any
commutative semiring, including a subsingleton semiring.
-/

@[expose] public section
noncomputable section
open Module
universe u v
namespace MvPolynomial

/-- Coordinate indices are exactly the native monomial exponents of degree one. -/
def degreeOneExponentEquiv (ι : Type v) :
    ι ≃ {a : ι →₀ ℕ // a.degree = 1} :=
  Equiv.ofBijective (fun i => ⟨Finsupp.single i 1, by simp⟩) (by
    constructor
    · intro i j h
      exact Finsupp.single_left_injective one_ne_zero (congrArg Subtype.val h)
    · intro a
      have h : a.val ∈ Set.range (fun i : ι => Finsupp.single i 1) := by
        rw [Finsupp.range_single_one]
        exact a.property
      obtain ⟨i, hi⟩ := h
      exact ⟨i, Subtype.ext hi⟩)

@[simp]
theorem degreeOneExponentEquiv_val (ι : Type v) (i : ι) :
    (degreeOneExponentEquiv ι i).val = Finsupp.single i 1 := rfl

variable (R : Type u) [CommSemiring R] (ι : Type v)

/-- The actual homogeneous degree-one submodule has the original coordinates as its basis. -/
def homogeneousDegreeOneBasis : Basis ι R (homogeneousSubmodule ι R 1) :=
  (Basis.span (linearIndependent_X (R := R) (σ := ι))).map
    (LinearEquiv.ofEq _ _ homogeneousSubmodule_one_eq_span_X.symm)

@[simp]
theorem homogeneousDegreeOneBasis_val (i : ι) :
    (homogeneousDegreeOneBasis R ι i).val = X i := by
  simp [homogeneousDegreeOneBasis]

/-- The original native coefficient at `single i 1` is the coordinate in the degree-one basis. -/
theorem homogeneousDegreeOneBasis_repr (p : homogeneousSubmodule ι R 1) (i : ι) :
    (homogeneousDegreeOneBasis R ι).repr p i = p.val.coeff (Finsupp.single i 1) := by
  classical
  have h : (homogeneousDegreeOneBasis R ι).coord i =
      (lcoeff R (Finsupp.single i 1)).comp (homogeneousSubmodule ι R 1).subtype := by
    apply (homogeneousDegreeOneBasis R ι).ext
    intro j
    change ((homogeneousDegreeOneBasis R ι).repr (homogeneousDegreeOneBasis R ι j)) i =
      (homogeneousDegreeOneBasis R ι j).val.coeff (Finsupp.single i 1)
    rw [Basis.repr_self, homogeneousDegreeOneBasis_val, coeff_X]
    by_cases hji : j = i
    · subst j
      simp
    · have hs : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 :=
        fun h => hji (Finsupp.single_left_injective one_ne_zero h)
      simp [hji, hs]
  exact LinearMap.congr_fun h p

end MvPolynomial
