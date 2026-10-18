/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.ResiduePushforward
public import Mathlib.LinearAlgebra.DFinsupp

/-! # Actual finite-support residue pushforward for a finite Dedekind map -/

@[expose] public noncomputable section

namespace MilnorK.DedekindResidue

open IsDedekindDomain IsLocalRing AdicCompletion
attribute [local instance] Classical.decEq

universe u
variable (A S : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

/-- The actual residue-field norm at the contracted height-one prime. -/
def pointResidueNorm (n : ℕ) (q : HeightOneSpectrum S) :
    K (ResidueField (Localization.AtPrime q.asIdeal)) n →ₗ[ℤ]
      K (ResidueField (Localization.AtPrime (q.under A).asIdeal)) n := by
  let := Localization.basePrimeLocalAlgebra (q.under A).asIdeal q.asIdeal rfl
  let := Localization.basePrimeLocal_isLocalHom (q.under A).asIdeal q.asIdeal rfl
  let := Localization.basePrimeLocal_residueFinite (q.under A).asIdeal q.asIdeal rfl
  exact finiteExtensionNorm _ _ n

/-- Push a finitely supported family forward using the actual finite residue norms. -/
def residuePushforward (n : ℕ) :
    (Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n) →ₗ[ℤ]
      Π₀ p : HeightOneSpectrum A, K (ResidueField (Localization.AtPrime p.asIdeal)) n :=
  DFinsupp.lsum ℤ fun q =>
    (DFinsupp.lsingle (q.under A)).comp (pointResidueNorm A S n q)

omit [Module.IsTorsionFree A S] in
@[simp] theorem residuePushforward_single (n : ℕ) (q : HeightOneSpectrum S)
    (x : K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n (DFinsupp.single q x) =
      DFinsupp.single (q.under A) (pointResidueNorm A S n q x) := by
  simp [residuePushforward]

/-- The original branches of `p` as original height-one points. -/
def branchPoint (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) : HeightOneSpectrum S :=
  ((Localization.heightOneOverEquivPrimesOver (S := S) p).symm
    ((Localization.primesOverEquivIdealBranch p.asIdeal p.ne_bot).symm q)).val

omit [Module.Finite A S]
  [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))] in
@[simp] theorem branchPoint_asIdeal (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    (branchPoint A S p q).asIdeal = q.val := rfl

omit [∀ p : HeightOneSpectrum A, CharZero (ResidueField (Localization.AtPrime p.asIdeal))] in
@[simp] theorem branchPoint_under (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    (branchPoint A S p q).under A = p := by
  apply HeightOneSpectrum.ext
  exact Localization.originalIdealBranch_under p q

/-- A branch contribution, with the original local scalar map. -/
def branchCoordinateNorm (p : HeightOneSpectrum A) (n : ℕ)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    K (ResidueField (Localization.AtPrime (branchPoint A S p q).asIdeal)) n →ₗ[ℤ]
      K (ResidueField (Localization.AtPrime p.asIdeal)) n := by
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  exact finiteExtensionNorm (ResidueField (Localization.AtPrime p.asIdeal))
    (ResidueField (Localization.AtPrime q.val)) n

/-- The norm at a specified base point, with its actual localization map. -/
def pointResidueNormOver (p : HeightOneSpectrum A) (n : ℕ)
    (q : HeightOneSpectrum S) (h : q.under A = p) :
    K (ResidueField (Localization.AtPrime q.asIdeal)) n →ₗ[ℤ]
      K (ResidueField (Localization.AtPrime p.asIdeal)) n := by
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h)
  exact finiteExtensionNorm _ _ n

omit [Module.IsTorsionFree A S] in
theorem pointResidueNormOver_eq (p : HeightOneSpectrum A) (n : ℕ)
    (q : HeightOneSpectrum S) (h : q.under A = p)
    (x : K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    pointResidueNormOver A S p n q h x =
      (DFinsupp.single (β := fun p : HeightOneSpectrum A =>
        K (ResidueField (Localization.AtPrime p.asIdeal)) n) (q.under A)
        (pointResidueNorm A S n q x)) p := by
  subst p
  simp only [DFinsupp.single_eq_same]
  rfl

/-- Each branch summand agrees with the corresponding coordinate of the
single-point pushforward. -/
theorem branchCoordinateNorm_eq (p : HeightOneSpectrum A) (n : ℕ)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S)))
    (x : K (ResidueField (Localization.AtPrime (branchPoint A S p q).asIdeal)) n) :
    branchCoordinateNorm A S p n q x =
      (DFinsupp.single (β := fun p : HeightOneSpectrum A =>
        K (ResidueField (Localization.AtPrime p.asIdeal)) n) ((branchPoint A S p q).under A)
        (pointResidueNorm A S n (branchPoint A S p q) x)) p := by
  exact pointResidueNormOver_eq A S p n (branchPoint A S p q)
    (branchPoint_under A S p q) x

/-- The coordinate formula sums every original prime branch, and only those branches. -/
theorem residuePushforward_apply (p : HeightOneSpectrum A) (n : ℕ)
    (y : Π₀ q : HeightOneSpectrum S, K (ResidueField (Localization.AtPrime q.asIdeal)) n) :
    residuePushforward A S n y p =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        branchCoordinateNorm A S p n q (y (branchPoint A S p q)) := by
  classical
  have hi : Function.Injective (branchPoint A S p) := by
    intro q r h
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  have hm : (DFinsupp.lapply p).comp (residuePushforward A S n) =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        (branchCoordinateNorm A S p n q).comp (DFinsupp.lapply (branchPoint A S p q)) := by
    apply DFinsupp.lhom_ext
    intro Q x
    simp only [LinearMap.comp_apply, DFinsupp.lapply_apply, residuePushforward_single,
      LinearMap.sum_apply]
    by_cases h : Q.under A = p
    · let q := (Localization.primesOverEquivIdealBranch p.asIdeal p.ne_bot)
        (Localization.heightOneOverEquivPrimesOver p ⟨Q, congrArg HeightOneSpectrum.asIdeal h⟩)
      have hq : branchPoint A S p q = Q := rfl
      rw [Finset.sum_eq_single q]
      · rw [branchCoordinateNorm_eq, hq, DFinsupp.single_eq_same]
      · intro r _ hr
        have hne : branchPoint A S p r ≠ Q := by
          intro he
          exact hr (hi (he.trans hq.symm))
        simp only [DFinsupp.single_eq_of_ne hne]
        exact map_zero _
      · simp
    · rw [DFinsupp.single_eq_of_ne (Ne.symm h)]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro q _
      have hne : branchPoint A S p q ≠ Q := by
        intro he
        exact h (he ▸ branchPoint_under A S p q)
      simp only [DFinsupp.single_eq_of_ne hne]
      exact map_zero _
  simpa only [LinearMap.comp_apply, DFinsupp.lapply_apply, LinearMap.sum_apply]
    using LinearMap.congr_fun hm y

variable (F E : Type u) [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

/-- The actual norm-residue square as an equality of finitely supported families. -/
theorem totalResidue_finiteExtensionNorm (n : ℕ) (x : K E (n + 1)) :
    totalResidue A F n (finiteExtensionNorm F E (n + 1) x) =
      residuePushforward A S n (totalResidue S E n x) := by
  apply DFinsupp.ext
  intro p
  rw [totalResidue_apply, residuePushforward_apply,
    residue_finiteExtensionNorm_atPrime A S F E p n x]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- The finite-support norm-residue square, bundled as an equality of linear maps. -/
theorem totalResidue_comp_finiteExtensionNorm (n : ℕ) :
    (totalResidue A F n).comp (finiteExtensionNorm F E (n + 1)) =
      (residuePushforward A S n).comp (totalResidue S E n) := by
  apply LinearMap.ext
  intro x
  exact totalResidue_finiteExtensionNorm A S F E n x

end MilnorK.DedekindResidue
