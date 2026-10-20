/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.AdjoinRootNormEvaluation
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree

/-!
# Norm factorization by separable polynomial roots

Source: `R5Lab.Aglib.FieldTheory.Norm.RootFactorization`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
open Polynomial UniqueFactorizationMonoid
namespace Algebra.NormRootFactorization

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

theorem norm_one_sub_gen (pb : PowerBasis K L) :
    Algebra.norm K (1 - pb.gen) = (minpoly K pb.gen).eval 1 := by
  rw [Algebra.norm_eq_matrix_det pb.basis, map_sub, map_one]
  have hs : Matrix.scalar (Fin pb.dim) (1 : K) = 1 := map_one _
  rw [← hs, ← Matrix.eval_charpoly, charpoly_leftMulMatrix]

theorem prod_norm_one_sub_roots [DecidableEq K] (q : ℕ) (hq : 0 < q) (a : K) :
    ((normalizedFactors (X ^ q - C a)).map
      (fun p => Algebra.norm K (1 - AdjoinRoot.root p))).prod = 1 - a := by
  classical
  let P : K[X] := X ^ q - C a
  have hP : P.Monic := monic_X_pow_sub_C a hq.ne'
  have hf : (normalizedFactors P).prod = P := by
    simpa only [hP.leadingCoeff, C_1, one_mul] using
      leadingCoeff_mul_prod_normalizedFactors P
  calc
    _ = ((normalizedFactors P).map (fun p => p.eval 1)).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro p hp
      exact AdjoinRoot.norm_one_sub_root p ((Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp
        hp).2.1
    _ = (normalizedFactors P).prod.eval 1 := (eval_multiset_prod _ _).symm
    _ = P.eval 1 := congrArg (eval 1) hf
    _ = 1 - a := by simp [P]

theorem factor_root_power [DecidableEq K] (q : ℕ) (hq : 0 < q) (a : K)
    (p : K[X]) (hp : p ∈ normalizedFactors (X ^ q - C a)) :
    AdjoinRoot.root p ^ q = algebraMap K (AdjoinRoot p) a := by
  have hP : (X ^ q - C a).Monic := monic_X_pow_sub_C a hq.ne'
  obtain ⟨_, _, d, hd⟩ := (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp hp
  have hzero : (X ^ q - C a).aeval (AdjoinRoot.root p) = 0 := by
    rw [hd, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  exact sub_eq_zero.mp (by simpa using hzero)

theorem factor_separable [DecidableEq K] (q : ℕ) (hq : 0 < q) (a : K)
    (ha : a ≠ 0) (hqc : (q : K) ≠ 0)
    (p : K[X]) (hp : p ∈ normalizedFactors (X ^ q - C a)) : p.Separable := by
  have hP : (X ^ q - C a).Monic := monic_X_pow_sub_C a hq.ne'
  exact (separable_X_pow_sub_C a hqc ha).of_dvd
    ((Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp hp).2.2

section SimpleExtension
variable {F : Type*} [Field F] [Algebra K F]

theorem norm_one_sub_adjoin (x : F) (hx : IsIntegral K x) :
    Algebra.norm K (1 - IntermediateField.AdjoinSimple.gen K x) =
      (minpoly K x).eval 1 := by
  have hm : minpoly K (IntermediateField.AdjoinSimple.gen K x) = minpoly K x := by
    rw [← minpoly.algebraMap_eq (algebraMap (IntermediateField.adjoin K {x}) F).injective]
    rfl
  simpa only [IntermediateField.adjoin.powerBasis_gen, hm] using
    norm_one_sub_gen (IntermediateField.adjoin.powerBasis hx)

theorem norm_one_sub_adjoin_of_factor (p : K[X]) (hp : Irreducible p)
    (hpm : p.Monic) (x : F) (hx : p.aeval x = 0) :
    Algebra.norm K (1 - IntermediateField.AdjoinSimple.gen K x) = p.eval 1 := by
  rw [norm_one_sub_adjoin x ⟨p, hpm, hx⟩,
    ← minpoly.eq_of_irreducible_of_monic hp hx hpm]

theorem exists_separable_norm_factorization [DecidableEq K] [IsAlgClosed F]
    (q : ℕ) (hq : 0 < q) (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hqc : (q : K) ≠ 0) :
    ∃ roots : {p : K[X] // p ∈ normalizedFactors (X ^ q - C a)} → F,
      (∀ p, p.val.aeval (roots p) = 0 ∧
        roots p ^ q = algebraMap K F a ∧ roots p ≠ 0 ∧ roots p ≠ 1 ∧
        IsIntegral K (roots p) ∧ IsSeparable K (roots p) ∧
        FiniteDimensional K (IntermediateField.adjoin K {roots p}) ∧
        Algebra.IsSeparable K (IntermediateField.adjoin K {roots p})) ∧
      (((normalizedFactors (X ^ q - C a)).attach).map
        (fun p => Algebra.norm K (1 - IntermediateField.AdjoinSimple.gen K (roots p)))).prod
          = 1 - a := by
  classical
  let P : K[X] := X ^ q - C a
  let s := normalizedFactors P
  have hP : P.Monic := monic_X_pow_sub_C a hq.ne'
  have hs (p : {p : K[X] // p ∈ s}) : Irreducible p.val ∧ p.val.Monic ∧ p.val ∣ P :=
    (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp p.property
  have hr (p : {p : K[X] // p ∈ s}) : ∃ x : F, p.val.aeval x = 0 :=
    IsAlgClosed.exists_aeval_eq_zero F p.val (hs p).1.degree_pos.ne'
  choose roots hroots using hr
  refine ⟨roots, ?_, ?_⟩
  · intro p
    have hpow : roots p ^ q = algebraMap K F a := by
      obtain ⟨d, hd⟩ := (hs p).2.2
      have hz : P.aeval (roots p) = 0 := by rw [hd, map_mul, hroots, zero_mul]
      exact sub_eq_zero.mp (by simpa [P] using hz)
    have hi : IsIntegral K (roots p) := ⟨p.val, (hs p).2.1, hroots p⟩
    have hm : p.val = minpoly K (roots p) :=
      minpoly.eq_of_irreducible_of_monic (hs p).1 (hroots p) (hs p).2.1
    refine ⟨hroots p, hpow, ?_, ?_, hi, ?_,
      (IntermediateField.adjoin.powerBasis hi).finite, ?_⟩
    · intro hz
      have : algebraMap K F a = 0 := by simpa [hz, zero_pow hq.ne'] using hpow.symm
      exact ha ((algebraMap K F).injective (by simpa using this))
    · intro hz
      have : algebraMap K F a = algebraMap K F 1 := by simpa [hz] using hpow.symm
      exact ha1 ((algebraMap K F).injective this)
    · change (minpoly K (roots p)).Separable
      rw [← hm]
      exact factor_separable q hq a ha hqc p.val p.property
    · apply (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K F).2
      change (minpoly K (roots p)).Separable
      rw [← hm]
      exact factor_separable q hq a ha hqc p.val p.property
  · calc
      _ = (s.attach.map (fun p => p.val.eval 1)).prod := by
        apply congrArg Multiset.prod
        apply Multiset.map_congr rfl
        intro p hp
        exact norm_one_sub_adjoin_of_factor p.val (hs p).1 (hs p).2.1 (roots p) (hroots p)
      _ = (s.map (fun p => p.eval 1)).prod := by rw [Multiset.attach_map_val']
      _ = (s.map (fun p => Algebra.norm K (1 - AdjoinRoot.root p))).prod := by
        apply congrArg Multiset.prod
        apply Multiset.map_congr rfl
        intro p hp
        exact (AdjoinRoot.norm_one_sub_root p ((Polynomial.mem_normalizedFactors_iff
          hP.ne_zero).mp hp).2.1).symm
      _ = 1 - a := prod_norm_one_sub_roots q hq a

end SimpleExtension


end Algebra.NormRootFactorization
