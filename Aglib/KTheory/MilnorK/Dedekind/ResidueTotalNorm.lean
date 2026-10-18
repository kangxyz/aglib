/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResiduePushforward
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The actual finite sum of normed residues of a Dedekind model

The sum uses the proved finite support of the original residues. Each
coefficient is the actual finite field norm, in every Milnor degree.
-/

@[expose] public noncomputable section

namespace MilnorK.DedekindResidue

open IsLocalRing IsDedekindDomain

variable (k S E : Type*) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k S]
  [∀ q : HeightOneSpectrum S, FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))]
  [Field E] [Algebra S E] [IsFractionRing S E]

open scoped Classical in
/-- The actual finite residue norms summed on the dependent finite support. -/
def totalNorm (n : ℕ) :
    (Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n)
      →ₗ[ℤ] K k n :=
  DFinsupp.lsum ℤ fun q => finiteExtensionNorm k
    (ResidueField (Localization.AtPrime q.asIdeal)) n

omit [IsDedekindDomain S] in
open scoped Classical in
/-- The total norm is the literal sum over the actual residual support. -/
theorem totalNorm_eq_sum (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ q ∈ y.support,
      finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) := by
  simp only [totalNorm, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, DFinsupp.sum]

omit [IsDedekindDomain S] in
/-- The same actual total norm is the finitely supported sum over all points. -/
theorem totalNorm_eq_finsum (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    totalNorm k S n y = ∑ᶠ q : HeightOneSpectrum S,
      finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) := by
  classical
  rw [totalNorm_eq_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro q hq
  apply DFinsupp.mem_support_iff.mpr
  intro hy
  exact hq (by
    change finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n (y q) = 0
    rw [hy, map_zero])

/-- The original affine curve boundary sum, before adding its points at infinity. -/
def normedTotalResidue (n : ℕ) : K E (n + 1) →ₗ[ℤ] K k n :=
  (totalNorm k S n).comp (totalResidue S E n)

open scoped Classical in
/-- Every term is an original local residue followed by its actual residue-field norm. -/
theorem normedTotalResidue_eq_sum (n : ℕ) (x : K E (n + 1)) :
    normedTotalResidue k S E n x =
      ∑ q ∈ (totalResidue S E n x).support,
        finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n
          (DVR.residue (Localization.AtPrime q.asIdeal) E n x) := by
  exact totalNorm_eq_sum k S n (totalResidue S E n x)

end MilnorK.DedekindResidue
