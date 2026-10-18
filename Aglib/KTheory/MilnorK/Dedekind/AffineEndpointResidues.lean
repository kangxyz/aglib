/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineUnitSymbolResidues
public import Aglib.KTheory.MilnorK.Dedekind.AffineNormSpecialization

/-! # Original affine branch sums at the literal polynomial places -/

@[expose] public noncomputable section
namespace MilnorK.DedekindResidue

open Polynomial PolynomialResidue PolynomialDedekindResidue IsLocalRing IsDedekindDomain
attribute [local instance] Classical.decEq

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

local instance polynomialPointResidueCharZero (p : HeightOneSpectrum k[X]) :
    CharZero (ResidueField (Localization.AtPrime p.asIdeal)) :=
  charZero_of_injective_algebraMap
    (algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))).injective

/-- The literal polynomial residue of the original norm is its full original
branch sum, using the actual quotient identification and coefficient maps. -/
theorem residueAt_norm_eq_original_branch_sum (p : MonicIrreducible k)
    (n : ℕ) (x : K E (n + 1)) :
    residueAt p.val n (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      MilnorK.map n (Polynomial.LocalResidue.residueEquiv p.val).toRingHom
        (∑ q : AdicCompletion.IdealBranch ((point p).asIdeal.map (algebraMap k[X] S)),
          branchCoordinateNorm k[X] S (point p) n q
            (DVR.residue (Localization.AtPrime (branchPoint k[X] S (point p) q).asIdeal)
              E n x)) := by
  rw [← PolynomialDedekindResidue.totalResidue_point,
    totalResidue_finiteExtensionNorm k[X] S (RatFunc k) E,
    residuePushforward_apply]
  rfl

/-- All actual branch orders and reduced coordinate tuples are retained when a
last parameter is appended to global affine units. -/
theorem residueAt_norm_unit_symbol_last (p : MonicIrreducible k)
    (n : ℕ) (a : Fin n → Sˣ) (b : Eˣ) :
    residueAt p.val n (finiteExtensionNorm (RatFunc k) E (n + 1)
      (symbol (Fin.snoc (Units.map (algebraMap S E).toMonoidHom ∘ a) b))) =
      MilnorK.map n (Polynomial.LocalResidue.residueEquiv p.val).toRingHom
        (∑ q : AdicCompletion.IdealBranch ((point p).asIdeal.map (algebraMap k[X] S)),
          let Q := branchPoint k[X] S (point p) q
          branchCoordinateNorm k[X] S (point p) n q
            (MilnorK.K2.DVR.value (Localization.AtPrime Q.asIdeal) E (Additive.ofMul b) •
              symbol (Units.map ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
                (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ a))) := by
  rw [residueAt_norm_eq_original_branch_sum k S E]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [DedekindResidue.residue_ring_units_last]

end MilnorK.DedekindResidue
