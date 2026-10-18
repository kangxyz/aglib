/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.RingTheory.FittingIdeal.LocallyFree
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Fibre ranks and the rank stratification

Let `M` be a finitely generated module over a commutative ring `R`.

* `Module.fittingIdeal_eq_top_iff_finrank_le`: over a field, `Fitt_k(V) = K` if and only if
  `dim V ≤ k` (Stacks Project, Tag 07ZB).
* `Module.finrank_residueField_tensor_le_iff`: for a prime `p`, `dim_{κ(p)} κ(p) ⊗[R] M ≤ k` if
  and only if `Fitt_k(M) ⊄ p` (Stacks, Tag 07ZC, (1) ⇔ (2));
  `Module.finrank_extendScalars_residueField_le_iff` is the same for the fibre written as
  `ModuleCat.extendScalars`, with the module in any universe.
* `Module.setOf_finrank_residueField_tensor_eq_succ` and
  `Module.setOf_finrank_residueField_tensor_eq_zero`: the set of primes where the fibre
  `κ(p) ⊗[R] M` has dimension `r + 1` is `V(Fitt_r(M)) \ V(Fitt_{r+1}(M))`, and the set where it
  vanishes is the complement of `V(Fitt_0(M))`.
* `Module.fittingIdeal_map_eq_bot_and_eq_top_iff`: for a ring map `R → S`, all localizations of
  `S ⊗[R] M` at primes of `S` are free of rank `r` if and only if `Fitt_k(M) S = 0` for `k < r`
  and `Fitt_r(M) S = S` (Stacks, Tags 07ZA (3) and 07ZD, with freeness in stalkwise form). This
  is the algebraic content of the universal property of the Fitting stratum
  `V(Fitt_{r-1}(M)) ∩ D(Fitt_r(M))`.

Nitsure's own proof of the case `n = 0` of the flattening stratification (*Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 4.3, pp. 19–20) does not use Fitting
ideals: it cuts the stratum out locally by the entries of a minimal presentation. The Fitting
stratum is the global form with the same universal property. The scheme-level statement, that
`Spec S → Spec R` factors through the locally closed subscheme `V(Fitt_{r-1}) ∩ D(Fitt_r)` if and
only if `Fitt_{r-1}(M) S = 0` and `Fitt_r(M) S = S`, and the passage from stalkwise to
Zariski-local freeness are not part of this family.

The fibre-rank locus is not the locus where `M_p` is free: for `R = k[x]/(x²)` and `M = R/(x)`,
the unique prime lies in `V(Fitt_0) \ V(Fitt_1)` while `M_p = M` is not free. The free locus of
rank `r` is described stalkwise by `Module.fittingIdeal_eq_bot_and_eq_top_iff_of_isLocalRing`.
-/

@[expose] public section

open TensorProduct

universe v

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

/-- Over a field `K`, `Fitt_k(V) = K` if and only if `dim V ≤ k` (Stacks Project, Tag 07ZB). -/
theorem fittingIdeal_eq_top_iff_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {k : ℕ} : fittingIdeal K V k = ⊤ ↔ Module.finrank K V ≤ k := by
  rw [fittingIdeal_of_basis (Module.finBasis K V), Nat.card_fin]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false bot_ne_top h

/-- The image of an ideal in the residue field at a prime `p` is everything if and only if the
ideal is not contained in `p`. -/
private theorem map_algebraMap_residueField_eq_top_iff (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    I.map (algebraMap R p.ResidueField) = ⊤ ↔ ¬I ≤ p := by
  have h1 : I.map (algebraMap R p.ResidueField) = ⊥ ↔ I ≤ p := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.ker_algebraMap_residueField]
  rcases Ideal.eq_bot_or_top (I.map (algebraMap R p.ResidueField)) with h | h
  · rw [h] at h1 ⊢
    exact iff_of_false bot_ne_top (not_not.2 (h1.1 rfl))
  · rw [h] at h1 ⊢
    exact iff_of_true rfl fun hle => top_ne_bot (h1.2 hle)

/-- Stacks Project, Tag 07ZC, (1) ⇔ (2): for a prime `p`, the fibre `κ(p) ⊗[R] M` has dimension
at most `k` if and only if `Fitt_k(M) ⊄ p`. -/
theorem finrank_residueField_tensor_le_iff [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    {k : ℕ} :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] M) ≤ k ↔ ¬fittingIdeal R M k ≤ p := by
  rw [← fittingIdeal_eq_top_iff_finrank_le, fittingIdeal_baseChange,
    map_algebraMap_residueField_eq_top_iff]

/-- Stacks Project, Tag 07ZC, (1) ⇔ (2), for the residue-field base change written as an
extension of scalars: `dim κ(p) ⊗_R N ≤ k` if and only if `Fitt_k(N) ⊄ p`. -/
theorem finrank_extendScalars_residueField_le_iff (p : Ideal R) [p.IsPrime]
    (N : ModuleCat.{v} R) [Module.Finite R N] {k : ℕ} :
    Module.finrank p.ResidueField
        ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).obj N) ≤ k ↔
      ¬fittingIdeal R N k ≤ p := by
  have := ModuleCat.finite_extendScalars (algebraMap R p.ResidueField) N
  rw [← fittingIdeal_eq_top_iff_finrank_le, fittingIdeal_extendScalars,
    map_algebraMap_residueField_eq_top_iff]

/-- The fibre-rank stratum of rank `r + 1` is `V(Fitt_r(M)) \ V(Fitt_{r+1}(M))`. -/
theorem setOf_finrank_residueField_tensor_eq_succ [Module.Finite R M] (r : ℕ) :
    {p : PrimeSpectrum R |
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = r + 1} =
      PrimeSpectrum.zeroLocus (fittingIdeal R M r) \
        PrimeSpectrum.zeroLocus (fittingIdeal R M (r + 1)) := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have h1 := finrank_residueField_tensor_le_iff (M := M) p.asIdeal (k := r)
  have h2 := finrank_residueField_tensor_le_iff (M := M) p.asIdeal (k := r + 1)
  constructor
  · intro h
    refine ⟨?_, h2.1 h.le⟩
    by_contra hc
    have := h1.2 hc
    omega
  · rintro ⟨ha, hb⟩
    have := h2.2 hb
    have : ¬Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) ≤ r :=
      fun h => h1.1 h ha
    omega

/-- The fibre-rank stratum of rank `0` is the complement of `V(Fitt_0(M))`. -/
theorem setOf_finrank_residueField_tensor_eq_zero [Module.Finite R M] :
    {p : PrimeSpectrum R |
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) = 0} =
      (PrimeSpectrum.zeroLocus (fittingIdeal R M 0))ᶜ := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, ← finrank_residueField_tensor_le_iff p.asIdeal, Nat.le_zero]

/-- The algebraic content of the universal property of the rank-`r` Fitting stratum (Stacks
Project, Tags 07ZA (3) and 07ZD, with freeness in stalkwise form): for a ring map `R → S`, all
localizations of `S ⊗[R] M` at primes of `S` are free of rank `r` if and only if
`Fitt_k(M) S = 0` for `k < r` and `Fitt_r(M) S = S`. The factorization of `Spec S → Spec R`
through a scheme-level stratum is not stated here. -/
theorem fittingIdeal_map_eq_bot_and_eq_top_iff [Module.Finite R M] (S : Type*) [CommRing S]
    [Algebra R S] {r : ℕ} :
    ((∀ k < r, (fittingIdeal R M k).map (algebraMap R S) = ⊥) ∧
        (fittingIdeal R M r).map (algebraMap R S) = ⊤) ↔
      ∀ q : PrimeSpectrum S,
        q ∈ Module.freeLocus S (S ⊗[R] M) ∧ Module.rankAtStalk (S ⊗[R] M) q = r := by
  simp only [← fittingIdeal_baseChange S]
  exact fittingIdeal_eq_bot_and_eq_top_iff

end Module
