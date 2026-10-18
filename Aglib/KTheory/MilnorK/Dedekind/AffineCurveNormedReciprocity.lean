/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResidueNormPushforward
public import Aglib.KTheory.MilnorK.Dedekind.PolynomialTotalNorm

/-!
# Actual affine curve residue sum and the infinity residue of its field norm

The finite part uses every original height-one point of the finite Dedekind
model. The remaining infinity term is stated explicitly, not silently replaced
by an unproved geometric branch sum.
-/

@[expose] public noncomputable section

namespace MilnorK.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The normed sum at all original finite curve points cancels the actual
infinity residue of the original field norm. -/
theorem affine_normed_reciprocity (n : ℕ) (x : K E (n + 1)) :
    letI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    letI : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    normedTotalResidue k S E n x +
      InfinityResidue.residue k n (finiteExtensionNorm (RatFunc k) E (n + 1) x) = 0 := by
  let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
    (inferInstanceAs (Algebra.FiniteType k k[X]))
    (inferInstanceAs (Algebra.FiniteType k[X] S))
  let : ∀ q : HeightOneSpectrum S,
      FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
    fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
  let : ∀ p : HeightOneSpectrum k[X],
      CharZero (ResidueField (Localization.AtPrime p.asIdeal)) := fun p =>
    charZero_of_injective_algebraMap
      (algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))).injective
  rw [← normedTotalResidue_finiteExtensionNorm k k[X] S (RatFunc k) E n x]
  exact PolynomialDedekindResidue.normedTotalResidue_add_infinity k n _

end MilnorK.DedekindResidue
