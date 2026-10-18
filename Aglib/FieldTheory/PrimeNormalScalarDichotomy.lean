/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Scalar extension of prime-degree normal polynomials

The coefficient extension is arbitrary, not necessarily finite. Normality of
the original root field and characteristic zero are explicit.
-/

@[expose] public noncomputable section

namespace Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]

private theorem factor_splitting_and_degree {p : F[X]} (hp : p.Monic)
    (hi : Irreducible p) [Fact (Irreducible p)] [Normal F (AdjoinRoot p)]
    {q : K[X]} (hq : Irreducible q) (hd : q ∣ p.map (algebraMap F K)) :
    let _ : Fact (Irreducible q) := ⟨hq⟩
    ((p.map (algebraMap F (AdjoinRoot q))).Splits) ∧ q.natDegree ∣ p.natDegree := by
  let : Fact (Irreducible q) := ⟨hq⟩
  let : FiniteDimensional K (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
  let : FiniteDimensional F (AdjoinRoot p) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hroot : aeval (AdjoinRoot.root q) p = 0 := by
    rw [← aeval_map_algebraMap K]
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hd (AdjoinRoot.eval₂_root q)
  let e : AdjoinRoot p →ₐ[F] AdjoinRoot q :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot q)) (AdjoinRoot.root q) hroot
  let : Algebra (AdjoinRoot p) (AdjoinRoot q) := e.toRingHom.toAlgebra
  let : IsScalarTower F (AdjoinRoot p) (AdjoinRoot q) :=
    IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have hsplit : (p.map (algebraMap F (AdjoinRoot q))).Splits := by
    have hs := Normal.splits (inferInstance : Normal F (AdjoinRoot p)) (AdjoinRoot.root p)
    rw [AdjoinRoot.minpoly_root hi.ne_zero, hp.leadingCoeff, inv_one, C_1, mul_one] at hs
    simpa only [map_map, ← IsScalarTower.algebraMap_eq] using
      hs.map (algebraMap (AdjoinRoot p) (AdjoinRoot q))
  have hsK : ((p.map (algebraMap F K)).map (algebraMap K (AdjoinRoot q))).Splits := by
    simpa only [map_map, ← IsScalarTower.algebraMap_eq] using hsplit
  let : IsSplittingField K (AdjoinRoot q) (p.map (algebraMap F K)) := ⟨hsK, by
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := q)]
    apply Algebra.adjoin_mono
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_rootSet.mpr ⟨map_ne_zero hp.ne_zero, by rwa [aeval_map_algebraMap]⟩⟩
  let : Normal K (AdjoinRoot q) := Normal.of_isSplittingField (p.map (algebraMap F K))
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : IsGalois K (AdjoinRoot q) := ⟨⟩
  let : IsGalois F (AdjoinRoot p) := ⟨⟩
  let r := IntermediateField.restrictRestrictAlgEquivMapHom F (AdjoinRoot p) K (AdjoinRoot q)
  have hr : Function.Injective r := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    have hh := congrArg (fun s : Gal(AdjoinRoot p/F) =>
      algebraMap (AdjoinRoot p) (AdjoinRoot q) (s (AdjoinRoot.root p))) h
    have he : algebraMap (AdjoinRoot p) (AdjoinRoot q) (AdjoinRoot.root p) =
        AdjoinRoot.root q := by
      change e (AdjoinRoot.root p) = _
      exact AdjoinRoot.lift_root hroot
    simpa [r, he, IntermediateField.restrictRestrictAlgEquivMapHom,
      AlgEquiv.restrictNormalHom, AlgEquiv.restrictNormal_commutes, e] using hh
  refine ⟨hsplit, ?_⟩
  have hc := Subgroup.card_dvd_of_injective r hr
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    (AdjoinRoot.powerBasis hq.ne_zero).finrank, (AdjoinRoot.powerBasis hi.ne_zero).finrank] at hc
  exact hc

/-- A prime-degree normal irreducible polynomial either stays irreducible or
splits completely under any coefficient field extension. -/
theorem Monic.irreducible_map_or_splits_of_prime_normal {p : F[X]}
    (hp : p.Monic) (hi : Irreducible p) [Fact (Irreducible p)]
    [Normal F (AdjoinRoot p)] (hprime : p.natDegree.Prime) :
    Irreducible (p.map (algebraMap F K)) ∨ (p.map (algebraMap F K)).Splits := by
  have hne : p.map (algebraMap F K) ≠ 0 := map_ne_zero hp.ne_zero
  have hunit : ¬IsUnit (p.map (algebraMap F K)) := by
    intro h
    have hd := natDegree_eq_zero_of_isUnit h
    rw [Polynomial.natDegree_map] at hd
    exact (ne_of_gt hi.natDegree_pos) hd
  obtain ⟨q, hq, hd⟩ := WfDvdMonoid.exists_irreducible_factor hunit hne
  let : Fact (Irreducible q) := ⟨hq⟩
  obtain ⟨hsplit, hdeg⟩ := factor_splitting_and_degree hp hi hq hd
  rcases hprime.eq_one_or_self_of_dvd q.natDegree hdeg with hone | heq
  · right
    let : FiniteDimensional K (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
    have hfin : Module.finrank K (AdjoinRoot q) = 1 := by
      rw [(AdjoinRoot.powerBasis hq.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hone]
    apply Splits.of_splits_map (algebraMap K (AdjoinRoot q))
    · simpa only [map_map, ← IsScalarTower.algebraMap_eq] using hsplit
    · intro x _
      obtain ⟨c, hc⟩ :=
        (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot q) one_ne_zero).mp hfin x
      exact ⟨c, by simpa only [Algebra.smul_def, mul_one] using hc⟩
  · left
    exact (associated_of_dvd_of_natDegree_le hd hne
      (by simp only [Polynomial.natDegree_map, heq, le_refl])).irreducible hq

end Polynomial
