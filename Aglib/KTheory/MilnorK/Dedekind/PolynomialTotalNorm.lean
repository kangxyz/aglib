/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResidueTotalNorm
public import Aglib.KTheory.MilnorK.Dedekind.PolynomialResidue
public import Aglib.RingTheory.FiniteTypeLocalResidue

/-! # Rational reciprocity on the actual Dedekind prime points -/

@[expose] public noncomputable section

namespace MilnorK.PolynomialDedekindResidue

open Polynomial PolynomialResidue PolynomialNorm IsLocalRing IsDedekindDomain

variable (k : Type*) [Field k] [CharZero k]

instance polynomialLocalResidueFinite (q : HeightOneSpectrum k[X]) :
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k k[X] q.asIdeal

instance polynomialIrreducibleResidueFinite (p : k[X]) [Fact (Irreducible p)] :
    FiniteDimensional k (Polynomial.LocalResidue.ResidueField p) :=
  Localization.finiteType_localResidue_finite k k[X] (Ideal.span {p})

/-- The original prime residue norm is exactly the existing polynomial norm term. -/
theorem norm_totalResidue_point (p : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    finiteExtensionNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
      polynomialNorm n p (residueAt p.val n x) := by
  rw [finiteExtensionNorm_eq_presentation k _ n p
    (Polynomial.LocalResidue.residueEquiv p.val).symm, LinearMap.comp_apply]
  exact congrArg (polynomialNorm n p) (totalResidue_point p n x)

/-- Rational reciprocity retains the actual height-one prime residue groups. -/
theorem normedTotalResidue_add_infinity (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    DedekindResidue.normedTotalResidue k k[X] (RatFunc k) n x +
      InfinityResidue.residue k n x = 0 := by
  classical
  change DedekindResidue.totalNorm k k[X] n
    (DedekindResidue.totalResidue k[X] (RatFunc k) n x) + _ = _
  rw [DedekindResidue.totalNorm_eq_finsum, ← finsum_comp_equiv (pointEquiv (k := k))]
  have he : (∑ᶠ p : MonicIrreducible k,
      (fun q : HeightOneSpectrum k[X] =>
        finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n
          (DedekindResidue.totalResidue k[X] (RatFunc k) n x q)) (pointEquiv p)) =
      ∑ᶠ p : MonicIrreducible k, polynomialNorm n p (residueAt p.val n x) := by
    apply finsum_congr
    intro p
    exact norm_totalResidue_point k p n x
  rw [he]
  have hsum : (∑ᶠ p : MonicIrreducible k, polynomialNorm n p (residueAt p.val n x)) =
      ∑ p ∈ (PolynomialResidue.totalResidue n x).support,
        polynomialNorm n p (residueAt p.val n x) := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    apply DFinsupp.mem_support_iff.mpr
    intro hz
    exact hp (by
      change polynomialNorm n p (PolynomialResidue.totalResidue n x p) = 0
      rw [hz, map_zero])
  rw [hsum]
  exact finite_rational_reciprocity n x

end MilnorK.PolynomialDedekindResidue
