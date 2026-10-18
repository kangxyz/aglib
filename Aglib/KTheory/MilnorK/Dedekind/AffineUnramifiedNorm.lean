/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResidueDirectSum
public import Aglib.KTheory.MilnorK.Dedekind.PolynomialResidue
public import Aglib.KTheory.MilnorK.RationalExactness

/-! # Actual norms of unramified affine curve classes are constant -/

@[expose] public noncomputable section
namespace MilnorK.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The actual field norm of an everywhere unramified affine class lies in the
constant image, by the original all-branch residue square and Bass--Tate exactness. -/
theorem norm_mem_constant_range_of_totalResidue_zero (n : ℕ) (x : K E (n + 1))
    (hx : totalResidue S E n x = 0) :
    finiteExtensionNorm (RatFunc k) E (n + 1) x ∈
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) := by
  classical
  let : ∀ p : HeightOneSpectrum k[X],
      CharZero (ResidueField (Localization.AtPrime p.asIdeal)) := fun p =>
    charZero_of_injective_algebraMap
      (algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))).injective
  have hz : totalResidue k[X] (RatFunc k) n
      (finiteExtensionNorm (RatFunc k) E (n + 1) x) = 0 := by
    rw [totalResidue_finiteExtensionNorm k[X] S (RatFunc k) E, hx, map_zero]
  apply (PolynomialResidue.totalResidue_eq_zero_iff_mem_constant_range n _).mp
  apply DFinsupp.ext
  intro p
  rw [PolynomialResidue.totalResidue_apply,
    ← PolynomialDedekindResidue.totalResidue_point, hz]
  simp

/-- Every global ring-unit symbol has zero residue at every original point. -/
theorem totalResidue_ring_units (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    totalResidue S E n (symbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) = 0 := by
  apply (totalResidue_eq_zero_iff S E n _).mpr
  intro q
  have h := DVR.residue_ring_units (Localization.AtPrime q.asIdeal) E n
    (Units.map (algebraMap S (Localization.AtPrime q.asIdeal)).toMonoidHom ∘ a)
  convert h using 2
  apply congrArg symbol
  funext i
  apply Units.ext
  exact IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E (a i)

/-- Global coordinate-unit symbols on the original finite affine curve have a
constant field norm; no smoothness, normal-prime, or boundary premise is used. -/
theorem norm_ring_unit_symbol_mem_constant_range (n : ℕ) (a : Fin (n + 1) → Sˣ) :
    finiteExtensionNorm (RatFunc k) E (n + 1)
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ a)) ∈
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) :=
  norm_mem_constant_range_of_totalResidue_zero k S E n _ (totalResidue_ring_units S E n a)

end MilnorK.DedekindResidue
