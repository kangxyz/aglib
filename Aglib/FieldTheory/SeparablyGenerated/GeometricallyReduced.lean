/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Algebra.CharP.Algebra

/-!
# Geometrically reduced field extensions are generally separable

Finite Frobenius independence follows by taking roots in an algebraic closure
and using reducedness of its tensor product. The separating-basis argument is native.
-/

open scoped TensorProduct
open TensorProduct

@[expose] public noncomputable section

namespace Algebra

/-- Reduced geometric base change prevents a new finite Frobenius relation.
No perfectness of k is assumed. -/
theorem linearIndependent_pow_of_geometricallyReduced
    {k K ι : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] [Finite ι]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    {v : ι → K} (hv : LinearIndependent k v) :
    LinearIndependent k (fun i => v i ^ p) := by
  classical
  let := Fintype.ofFinite ι
  let D := AlgebraicClosure k ⊗[k] K
  let : IsReduced D := (Algebra.isGeometricallyReduced_field_iff k K).mp inferInstance
  let : ExpChar (AlgebraicClosure k) p := expChar_of_injective_algebraMap
    (RingHom.injective (algebraMap k (AlgebraicClosure k))) p
  let : ExpChar D p := expChar_of_injective_ringHom
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k)
      (A := AlgebraicClosure k) (B := K) (RingHom.injective (algebraMap k K))) p
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  choose d hd using fun i =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) (c i)) hp.pos
  have hpow : (∑ i, d i ⊗ₜ[k] v i : D) ^ p = 0 := by
    calc
      (∑ i, d i ⊗ₜ[k] v i : D) ^ p =
          ∑ i, (d i ^ p) ⊗ₜ[k] (v i ^ p) := by
        simpa only [Algebra.TensorProduct.tmul_pow] using
          (sum_pow_char p Finset.univ (fun i => (d i ⊗ₜ[k] v i : D)))
      _ = ∑ i, (algebraMap k (AlgebraicClosure k) (c i)) ⊗ₜ[k] (v i ^ p) := by
        simp only [hd]
      _ = (1 : AlgebraicClosure k) ⊗ₜ[k] (∑ i, c i • (v i ^ p)) := by
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← TensorProduct.smul_tmul]
        simp only [Algebra.smul_def, mul_one]
      _ = 0 := by rw [hc, TensorProduct.tmul_zero]
  have hz : (∑ i, d i ⊗ₜ[k] v i : D) = 0 := eq_zero_of_pow_eq_zero hpow
  have ht : LinearIndependent (AlgebraicClosure k)
      (fun i => (1 : AlgebraicClosure k) ⊗ₜ[k] v i) :=
    Module.Flat.linearIndependent_one_tmul hv
  have hd0 : ∀ i, d i = 0 := Fintype.linearIndependent_iff.mp ht d (by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hz)
  intro i
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [map_zero, ← hd i, hd0 i, zero_pow hp.ne_zero]

/-- The only separating-basis machinery used is the existing native theorem. -/
theorem isSeparablyGenerated_of_geometricallyReduced
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] [Algebra.EssFiniteType k K] :
    Algebra.IsSeparablyGenerated k K := by
  classical
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · infer_instance
  let : ExpChar k p := .prime hp.out
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := k) (K := K) p hp.out (fun s hs =>
        linearIndependent_pow_of_geometricallyReduced p hp.out hs)
  exact ⟨(s : Set K), hs, hsep⟩

/-- Arbitrary geometric reduced field extensions are generally separable.
In particular this is not a claim that K/k is algebraic. -/
theorem isTranscendentalSeparable_of_geometricallyReduced
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] :
    Algebra.IsTranscendentalSeparable k K := by
  refine ⟨fun L hL => ?_⟩
  let := hL
  let : Algebra.IsGeometricallyReduced k L :=
    Algebra.IsGeometricallyReduced.of_injective L.val L.val.injective
  exact isSeparablyGenerated_of_geometricallyReduced k L

end Algebra
