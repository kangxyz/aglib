/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Length.ResidueDimension
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Artinian/FiniteAlgebra.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8fd5bc5d5d1aa35ba5f3d5d1fd24acafac94114789f9d668d5687480e5bd776b`.
-/

@[expose] public section

noncomputable section
open IsLocalRing
namespace Algebra
section ArtinianComponents

variable (B : Type*) [CommRing B]

/-- Powers of a maximal ideal have a local quotient, with no reducedness hypothesis. -/
theorem quotient_pow_isLocalRing (m : Ideal B) [m.IsMaximal] (n : ℕ) (hn : n ≠ 0) :
    IsLocalRing (B ⧸ m ^ n) := by
  have hne : m ^ n ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))
      (Ideal.pow_le_self (I := m) hn)
  let : Nontrivial (B ⧸ m ^ n) := Ideal.Quotient.nontrivial_iff.mpr hne
  obtain ⟨J, hJ, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal (B ⧸ m ^ n)) bot_ne_top
  have H (Q : Ideal (B ⧸ m ^ n)) (hQ : Q.IsMaximal) :
      Ideal.comap (Ideal.Quotient.mk (m ^ n)) Q = m := by
    let := hQ
    let : (Ideal.comap (Ideal.Quotient.mk (m ^ n)) Q).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    apply Eq.symm
    apply Ideal.IsMaximal.eq_of_le (inferInstance : m.IsMaximal)
      (Ideal.IsMaximal.ne_top inferInstance)
    apply Ideal.IsPrime.le_of_pow_le
    simpa only [Ideal.mk_ker] using
      (Ideal.ker_le_comap (K := Q) (Ideal.Quotient.mk (m ^ n)))
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, ?_⟩
  intro Q hQ
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  exact (H Q hQ).trans (H J hJ).symm

/-- A positive maximal-ideal-power component, preserving nilpotent multiplicities. -/
abbrev ArtinComponent (n : ℕ) (m : MaximalSpectrum B) := B ⧸ m.asIdeal ^ (n + 1)

instance artinComponent_isLocalRing (n : ℕ) (m : MaximalSpectrum B) :
    IsLocalRing (ArtinComponent B n m) := by
  let := m.isMaximal
  exact quotient_pow_isLocalRing B m.asIdeal (n + 1) (Nat.succ_ne_zero n)

variable (k : Type*) [Field k] [Algebra k B]

/-- Reduction of the primary component induces the canonical residue-field
equivalence with the original maximal quotient, preserving the base scalars. -/
def artinComponentResidueEquiv (n : ℕ) (m : MaximalSpectrum B) :
    ResidueField (ArtinComponent B n m) ≃ₐ[k] B ⧸ m.asIdeal := by
  let := m.isMaximal
  letI := Ideal.Quotient.field m.asIdeal
  let C := ArtinComponent B n m
  let h : m.asIdeal ^ (n + 1) ≤ m.asIdeal :=
    Ideal.pow_le_self (I := m.asIdeal) (Nat.succ_ne_zero n)
  let φ : C →ₐ[k] B ⧸ m.asIdeal := Ideal.Quotient.factorₐ k h
  let : IsLocalHom φ.toRingHom :=
    IsLocalHom.of_surjective φ.toRingHom (Ideal.Quotient.factor_surjective h)
  let l : ResidueField C →ₐ[k] B ⧸ m.asIdeal := {
    toRingHom := IsLocalRing.ResidueField.lift φ.toRingHom
    commutes' := by
      intro a
      change IsLocalRing.ResidueField.lift φ.toRingHom
        (residue C (algebraMap k C a)) = algebraMap k (B ⧸ m.asIdeal) a
      rw [IsLocalRing.ResidueField.lift_residue_apply]
      exact φ.commutes a }
  refine AlgEquiv.ofBijective l ⟨l.toRingHom.injective, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := Ideal.Quotient.factor_surjective h y
  refine ⟨residue C z, ?_⟩
  change IsLocalRing.ResidueField.lift φ.toRingHom (residue C z) = y
  rw [IsLocalRing.ResidueField.lift_residue_apply]
  exact hz

variable [Module.Finite k B]

/-- The full finite algebra dimension is the sum of local Artinian lengths times
their actual residue degrees. The positive exponent is supplied by nilradical
nilpotence; the algebra is not replaced by its reduced quotient. -/
theorem exists_finrank_eq_sum_component_length :
    let : IsArtinianRing B := IsArtinianRing.of_finite k B
    let := Fintype.ofFinite (MaximalSpectrum B)
    ∃ n : ℕ, Module.finrank k B =
      ∑ m : MaximalSpectrum B,
        (Module.length (ArtinComponent B n m) (ArtinComponent B n m)).toNat *
          Module.finrank k (ResidueField (ArtinComponent B n m)) := by
  classical
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  let := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  have hz : nilradical B ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]
  let e : B ≃ₐ[B] ∀ m : MaximalSpectrum B, ArtinComponent B n m :=
    (AlgEquiv.quotientBot B B).symm.trans
      ((Ideal.quotientEquivAlgOfEq B hz.symm).trans
        (IsArtinianRing.quotNilradicalPowEquivPi (R := B) (n + 1)))
  refine ⟨n, ?_⟩
  calc
    Module.finrank k B = Module.finrank k (∀ m : MaximalSpectrum B, ArtinComponent B n m) :=
      (e.toLinearEquiv.restrictScalars k).finrank_eq
    _ = ∑ m : MaximalSpectrum B, Module.finrank k (ArtinComponent B n m) :=
      Module.finrank_pi_fintype k
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Module.finrank_eq_local_length_mul_residue_finrank k
        (ArtinComponent B n m) (ArtinComponent B n m)
      exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The same full nonreduced dimension formula with the original maximal-quotient
residue degrees, on their actual quotient scalar maps. -/
theorem exists_finrank_eq_sum_maximal_quotient_degree :
    let : IsArtinianRing B := IsArtinianRing.of_finite k B
    let := Fintype.ofFinite (MaximalSpectrum B)
    ∃ n : ℕ, Module.finrank k B =
      ∑ m : MaximalSpectrum B,
        (Module.length (ArtinComponent B n m) (ArtinComponent B n m)).toNat *
          Module.finrank k (B ⧸ m.asIdeal) := by
  classical
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  let := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨n, hn⟩ := exists_finrank_eq_sum_component_length B k
  refine ⟨n, hn.trans ?_⟩
  apply Finset.sum_congr rfl
  intro m _
  rw [(artinComponentResidueEquiv B k n m).toLinearEquiv.finrank_eq]

end ArtinianComponents
end Algebra
