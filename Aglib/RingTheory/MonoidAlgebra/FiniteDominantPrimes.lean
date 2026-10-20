/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Aglib.RingTheory.Ideal.MinimalPrime.GoingDown

/-!
# Finite dominant primes of the two-coordinate Laurent algebra

The coordinate order is the literal ordered pair `ℤ × ℤ`. The carrier requires only a
commutative ring; domain and Noetherian hypotheses belong to the results that use them.

## Migration source

The carrier and its structural projections are extracted from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/SupportPoints.lean`:29–35 at R5
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d97baddff914894d7325740a5ea5068f1463bfb6172ce6442e7758eef5be3fec`.
The quotient torsion-freeness proof is extracted from
`lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/DominantFibres.lean`:44–53
at the same revision, SHA-256
`feb98980155e255608042440f62d140ae61d399b41ffda5ff4f2a096da2dfc0e`.
The normal-domain contraction theorem is extracted from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalRegularity.lean`:116–121,
SHA-256 `8988bdbfdd8f35a20f7598b58a9d4de4e725c3f461240ac33233f0895ba1ec78`,
at that same revision. Operator coefficients and scheme adapters use this carrier.
-/

@[expose] public section

namespace MonoidAlgebra

universe u

/-- A prime quotient of the ordered two-coordinate Laurent algebra, finite and dominant
over the coefficient ring. -/
def FiniteDominantPrime (R : Type u) [CommRing R] :=
  {p : Ideal (MonoidAlgebra R (Multiplicative (ℤ × ℤ))) //
    p.IsPrime ∧ Module.Finite R (MonoidAlgebra R (Multiplicative (ℤ × ℤ)) ⧸ p) ∧
      p.under R = ⊥}

namespace FiniteDominantPrime

variable {R : Type u} [CommRing R]

instance isPrime (p : FiniteDominantPrime R) : p.val.IsPrime := p.property.1

instance finite (p : FiniteDominantPrime R) :
    Module.Finite R (MonoidAlgebra R (Multiplicative (ℤ × ℤ)) ⧸ p.val) :=
  p.property.2.1

theorem under_eq_bot (p : FiniteDominantPrime R) : p.val.under R = ⊥ := p.property.2.2

/-- Dominance gives torsion-freeness of the literal prime quotient over a domain. -/
theorem quotient_torsionFree [IsDomain R] (p : FiniteDominantPrime R) :
    Module.IsTorsionFree R (MonoidAlgebra R (Multiplicative (ℤ × ℤ)) ⧸ p.val) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  rw [RingHom.injective_iff_ker_eq_bot]
  ext r
  rw [Ideal.mem_bot]
  change Ideal.Quotient.mk p.val (algebraMap R (MonoidAlgebra R (Multiplicative (ℤ × ℤ))) r) =
    0 ↔ r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r ∈ p.val.under R ↔ r = 0
  rw [under_eq_bot p, Ideal.mem_bot]

/-- Over a normal domain, a minimal prime over an extended base prime contracts to
that prime. Finiteness and dominance supply the actual integral torsion-free algebra;
no flatness, projectivity or Noetherian hypothesis is imposed. -/
theorem minimalPrime_under_eq [IsDomain R] [IsIntegrallyClosed R]
    (p : FiniteDominantPrime R) (J : Ideal R) [J.IsPrime]
    (Q : Ideal (MonoidAlgebra R (Multiplicative (ℤ × ℤ)) ⧸ p.val))
    (hQ : Q ∈ (J.map (algebraMap R
      (MonoidAlgebra R (Multiplicative (ℤ × ℤ)) ⧸ p.val))).minimalPrimes) :
    Q.under R = J := by
  let := quotient_torsionFree p
  exact Ideal.normal_integral_minimalPrime_contract J Q hQ

end FiniteDominantPrime

end MonoidAlgebra
