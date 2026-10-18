/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResidueTotalNorm
public import Aglib.KTheory.MilnorK.Dedekind.ResidueDirectSum

/-! # Normed original residue sums under a finite map -/

@[expose] public noncomputable section

namespace MilnorK.DedekindResidue

open IsDedekindDomain IsLocalRing
attribute [local instance] Classical.decEq

universe u
variable (k A S : Type u) [Field k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]
  [Module.Finite A S] [Module.IsTorsionFree A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))]
  [∀ p : HeightOneSpectrum A, FiniteDimensional k (ResidueField (Localization.AtPrime p.asIdeal))]
  [∀ q : HeightOneSpectrum S, FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))]

omit [Module.IsTorsionFree A S] in
/-- Summing the original residue norms commutes with actual finite-point pushforward. -/
theorem totalNorm_comp_residuePushforward (n : ℕ) :
    (totalNorm k A n).comp (residuePushforward A S n) = totalNorm k S n := by
  apply DFinsupp.lhom_ext
  intro q x
  simp only [LinearMap.comp_apply, residuePushforward_single]
  simp only [totalNorm, DFinsupp.lsum_single]
  let := Localization.basePrimeLocalAlgebra (q.under A).asIdeal q.asIdeal rfl
  let := Localization.basePrimeLocalTower (q.under A).asIdeal q.asIdeal rfl
  let := Localization.basePrimeLocal_isLocalHom (q.under A).asIdeal q.asIdeal rfl
  let := Localization.basePrimeLocal_residueFinite (q.under A).asIdeal q.asIdeal rfl
  let : IsScalarTower k (Localization.AtPrime (q.under A).asIdeal)
      (Localization.AtPrime q.asIdeal) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply k A (Localization.AtPrime (q.under A).asIdeal),
      ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (q.under A).asIdeal),
      ← IsScalarTower.algebraMap_apply k A]
  let : CharZero (ResidueField (Localization.AtPrime (q.under A).asIdeal)) :=
    ‹∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))›
      (q.under A)
  let : FiniteDimensional k (ResidueField (Localization.AtPrime (q.under A).asIdeal)) :=
    ‹∀ p : HeightOneSpectrum A,
      FiniteDimensional k (ResidueField (Localization.AtPrime p.asIdeal))› (q.under A)
  let : FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
    ‹∀ q : HeightOneSpectrum S,
      FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal))› q
  dsimp only [pointResidueNorm]
  have ht := finiteExtensionNorm_tower (k := k)
    (ResidueField (Localization.AtPrime (q.under A).asIdeal))
    (ResidueField (Localization.AtPrime q.asIdeal)) n x
  with_reducible exact ht.symm

variable (F E : Type u) [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

/-- The global finite-support boundary sum agrees with that of the field norm. -/
theorem normedTotalResidue_finiteExtensionNorm (n : ℕ) (x : K E (n + 1)) :
    normedTotalResidue k A F n (finiteExtensionNorm F E (n + 1) x) =
      normedTotalResidue k S E n x := by
  unfold normedTotalResidue
  simp only [LinearMap.comp_apply]
  rw [totalResidue_finiteExtensionNorm A S F E]
  exact LinearMap.congr_fun (totalNorm_comp_residuePushforward k A S n)
    (totalResidue S E n x)

end MilnorK.DedekindResidue
