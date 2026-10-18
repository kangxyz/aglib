/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.DVR
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Data.DFinsupp.Module

/-!
# Finite support of actual Dedekind-domain residues

The original fraction field is retained. Nonzero numerator and denominator
principal ideals have finitely many prime factors. Away from those factors a
fraction is a local unit, so every all-unit symbol has zero actual DVR residue.
Symbol generation then proves finite support for every Milnor class.
-/

@[expose] public noncomputable section

namespace MilnorK.DedekindResidue

open IsDedekindDomain

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

/-- The canonical map from a prime localization to the original fraction field. -/
instance fractionAlgebra (q : HeightOneSpectrum S) : Algebra (Localization.AtPrime q.asIdeal) E :=
  (IsLocalization.lift (S := Localization.AtPrime q.asIdeal)
    (fun s : q.asIdeal.primeCompl => IsUnit.mk0 (algebraMap S E s) (by
      intro h
      have hz : (s : S) = 0 := (IsFractionRing.injective S E) (by simpa using h)
      exact nonZeroDivisors.ne_zero
        (q.asIdeal.primeCompl_le_nonZeroDivisors s.property) hz))).toAlgebra

instance fractionTower (q : HeightOneSpectrum S) :
    IsScalarTower S (Localization.AtPrime q.asIdeal) E := by
  apply IsScalarTower.of_algebraMap_eq
  intro s
  exact (IsLocalization.lift_eq _ s).symm

instance fractionRing (q : HeightOneSpectrum S) :
    IsFractionRing (Localization.AtPrime q.asIdeal) E :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) E

instance localDVR (q : HeightOneSpectrum S) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot _

/-- Only finitely many height-one primes contain a nonzero element. -/
theorem finite_primes_containing (s : S) (hs : s ≠ 0) :
    Set.Finite {q : HeightOneSpectrum S | s ∈ q.asIdeal} := by
  have h := Ideal.finite_factors (R := S)
    (I := Ideal.span {s}) (by simpa using hs)
  simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using h

/-- Every fraction-field unit lifts to a local unit outside a finite set of primes. -/
theorem finite_nonlocal_units (a : Eˣ) :
    Set.Finite {q : HeightOneSpectrum S |
      ¬ ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
        MilnorK.K2.DVR.fieldUnits (Localization.AtPrime q.asIdeal) E u = a} := by
  obtain ⟨s, t, ht, hst⟩ := IsFractionRing.div_surjective S (a : E)
  have hs : s ≠ 0 := by
    intro h
    simp only [h, map_zero, zero_div] at hst
    exact a.ne_zero hst.symm
  refine ((finite_primes_containing S s hs).union
    (finite_primes_containing S t (nonZeroDivisors.ne_zero ht))).subset ?_
  intro q hq
  by_contra h
  have hs' : s ∈ q.asIdeal.primeCompl := fun hm => h (Or.inl hm)
  have ht' : t ∈ q.asIdeal.primeCompl := fun hm => h (Or.inr hm)
  let us := (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨s, hs'⟩).unit
  let ut := (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨t, ht'⟩).unit
  apply hq
  refine ⟨us / ut, ?_⟩
  rw [map_div]
  apply Units.ext
  simp only [Units.val_div_eq_div_val, MilnorK.K2.DVR.fieldUnits, Units.coe_map,
    us, ut, IsUnit.unit_spec]
  change algebraMap (Localization.AtPrime q.asIdeal) E
      (algebraMap S (Localization.AtPrime q.asIdeal) s) /
    algebraMap (Localization.AtPrime q.asIdeal) E
      (algebraMap S (Localization.AtPrime q.asIdeal) t) = (a : E)
  simpa only [← IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E] using hst

/-- Every actual symbol has finite residue support in every positive degree. -/
theorem finite_residue_symbol_support (n : ℕ) (a : SymbolTuple E (n + 1)) :
    Set.Finite {q : HeightOneSpectrum S |
      DVR.residue (Localization.AtPrime q.asIdeal) E n (symbol a) ≠ 0} := by
  classical
  have h := Set.finite_iUnion (fun i => finite_nonlocal_units S E (a i))
  refine h.subset ?_
  intro q hq
  by_contra h
  have hu : ∀ i, ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
      MilnorK.K2.DVR.fieldUnits (Localization.AtPrime q.asIdeal) E u = a i := by
    intro i
    by_contra hi
    exact h (Set.mem_iUnion.mpr ⟨i, hi⟩)
  choose u hu using hu
  apply hq
  have ha : a = MilnorK.K2.DVR.fieldUnits (Localization.AtPrime q.asIdeal) E ∘ u := by
    funext i
    exact (hu i).symm
  rw [ha]
  exact DVR.residue_ring_units _ E n u

/-- Classes with finite actual support form an integer submodule. -/
private def finiteResidueSubmodule (n : ℕ) : Submodule ℤ (K E (n + 1)) where
  carrier := {x | Set.Finite {q : HeightOneSpectrum S |
    DVR.residue (Localization.AtPrime q.asIdeal) E n x ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro q hq
    by_contra h
    have hx0 : DVR.residue (Localization.AtPrime q.asIdeal) E n x = 0 := by
      simpa using fun hn => h (Or.inl hn)
    have hy0 : DVR.residue (Localization.AtPrime q.asIdeal) E n y = 0 := by
      simpa using fun hn => h (Or.inr hn)
    exact hq (by rw [map_add, hx0, hy0, add_zero])
  smul_mem' := by
    intro z x hx
    refine hx.subset ?_
    intro q hq hx0
    exact hq (by rw [map_smul, hx0, smul_zero])

/-- Actual DVR residues of every original fraction-field class have finite support. -/
theorem finite_residue_support (n : ℕ) (x : K E (n + 1)) :
    Set.Finite {q : HeightOneSpectrum S |
      DVR.residue (Localization.AtPrime q.asIdeal) E n x ≠ 0} := by
  have h : (finiteResidueSubmodule S E n).mkQ = 0 := by
    apply MilnorK.linearMap_ext
    intro a
    change (Submodule.Quotient.mk (symbol a) : K E (n + 1) ⧸
      finiteResidueSubmodule S E n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (finite_residue_symbol_support S E n a)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

instance residueAddCommGroup (n : ℕ) :
    (q : HeightOneSpectrum S) → AddCommGroup (K (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n) := fun _ => inferInstance

instance residueModule (n : ℕ) :
    (q : HeightOneSpectrum S) → Module ℤ (K (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n) := fun _ => inferInstance

/-- The actual total residue, with finite support proved for every class. -/
def totalResidue (n : ℕ) : K E (n + 1) →ₗ[ℤ]
    Π₀ q : HeightOneSpectrum S, K (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n where
  toFun x := ⟨fun q => DVR.residue (Localization.AtPrime q.asIdeal) E n x,
    Trunc.mk ⟨(finite_residue_support S E n x).toFinset.val, fun q => by
      classical
      by_cases hq : DVR.residue (Localization.AtPrime q.asIdeal) E n x = 0
      · exact Or.inr hq
      · exact Or.inl ((finite_residue_support S E n x).mem_toFinset.mpr hq)⟩⟩
  map_add' x y := by
    apply DFinsupp.ext
    intro q
    exact map_add (DVR.residue (Localization.AtPrime q.asIdeal) E n) x y
  map_smul' z x := by
    apply DFinsupp.ext
    intro q
    exact map_smul (DVR.residue (Localization.AtPrime q.asIdeal) E n) z x

/-- Each total-residue coordinate is the original DVR residue, literally. -/
@[simp] theorem totalResidue_apply (n : ℕ) (x : K E (n + 1))
    (q : HeightOneSpectrum S) :
    totalResidue S E n x q = DVR.residue (Localization.AtPrime q.asIdeal) E n x := rfl

/-- The total residue vanishes precisely when every local residue vanishes. -/
theorem totalResidue_eq_zero_iff (n : ℕ) (x : K E (n + 1)) :
    totalResidue S E n x = 0 ↔ ∀ q : HeightOneSpectrum S,
      DVR.residue (Localization.AtPrime q.asIdeal) E n x = 0 := by
  constructor
  · intro h q
    exact DFunLike.congr_fun h q
  · intro h
    exact DFinsupp.ext h

end MilnorK.DedekindResidue
