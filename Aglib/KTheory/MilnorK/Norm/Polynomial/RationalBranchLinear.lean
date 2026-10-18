/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalTranslation
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalLinear
public import Aglib.FieldTheory.PrimeNormalScalarDichotomy
public import Aglib.RingTheory.AdjoinRootScalarBranches

/-!
# Linear-place norm squares for every prime-normal scalar branch

The linear constant presentations and the prime-degree normal presentations
satisfy the same actual rational-function residue square at every linear
place. Every scalar branch of a prime-normal presentation is one of these
cases, and its required normality is derived from its literal divisibility.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue AdjoinRoot

variable {k H : Type*} [Field k] [Field H]

local instance (a : k) : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩
local instance (p : MonicIrreducible k) (a : AdjoinRoot p.val) :
    Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- Every linear place has the original evaluated residue square for a
linear constant presentation, on arbitrary classes in all Milnor degrees. -/
theorem residueAt_linear_rationalFunctionNorm_linear [CharZero k]
    (p : MonicIrreducible k) (hp : p.val.natDegree = 1) (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (linearRootEquiv (algebraMap k (AdjoinRoot p.val) a)).toRingHom
          (residueAt (X - C (algebraMap k (AdjoinRoot p.val) a)) n x)) := by
  rw [residueAt_linear_eq_residueAt_X_translation a, rationalFunctionNorm_translation,
    residueAt_X_rationalFunctionNorm_linear_normalized p hp,
    ← residueAt_linear_eq_residueAt_X_translation]

/-- Each actual scalar branch has degree one or the original prime degree;
no branch is omitted in the split case. -/
theorem scalarBranch_natDegree_eq_one_or_prime [CharZero k] [Algebra k H]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime)
    (q : IrreducibleBranch (p.val.map (algebraMap k H))) :
    q.val.val.natDegree = 1 ∨ q.val.val.natDegree.Prime := by
  rcases p.property.1.irreducible_map_or_splits_of_prime_normal
    (K := H) p.property.2 hp with hi | hs
  · right
    have he : q.val.val = p.val.map (algebraMap k H) :=
      eq_of_monic_of_associated q.val.property.1 (p.property.1.map _)
        (q.val.property.2.associated_of_dvd hi q.property)
    simpa only [he, Polynomial.natDegree_map] using hp
  · left
    have hq := hs.of_dvd (Polynomial.map_ne_zero p.property.2.ne_zero) q.property
    exact hq.natDegree_eq_one_of_irreducible q.val.property.2

/-- Every actual scalar branch of a prime-normal presentation satisfies the
linear-place square. Normality and the degree alternatives are derived, not
supplied as branch-specific hypotheses. -/
theorem residueAt_linear_rationalFunctionNorm_scalarBranch [CharZero k] [Algebra k H]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime)
    (q : IrreducibleBranch (p.val.map (algebraMap k H))) (a : H) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot q.val.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) q.val x)) =
      polynomialNorm n q.val
        (map n (linearRootEquiv (algebraMap H (AdjoinRoot q.val.val) a)).toRingHom
          (residueAt (X - C (algebraMap H (AdjoinRoot q.val.val) a)) n x)) := by
  let : CharZero H := charZero_of_injective_algebraMap (algebraMap k H).injective
  let : Normal H (AdjoinRoot q.val.val) :=
    AdjoinRoot.normal_of_dvd_map p.property.1 q.property
  rcases scalarBranch_natDegree_eq_one_or_prime p hp q with hq | hq
  · exact residueAt_linear_rationalFunctionNorm_linear q.val hq a n x
  · exact residueAt_linear_rationalFunctionNorm_prime q.val hq a n x

end MilnorK.PolynomialNorm
