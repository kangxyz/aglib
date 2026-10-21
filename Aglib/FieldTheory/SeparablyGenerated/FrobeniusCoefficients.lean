/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.GeometricallyReduced

/-!
# Frobenius coefficient independence under geometrically reduced field extension

This is a coefficient-extension statement, not an excellence or completion theorem.
-/

open scoped TensorProduct
open TensorProduct

@[expose] public noncomputable section

namespace Algebra

/-- A finite family independent over the literal Frobenius subfield remains
independent over the larger Frobenius subfield after geometrically reduced
extension of the coefficient field. -/
theorem linearIndependent_frobeniusFieldRange_map_of_geometricallyReduced
    {k L ι : Type*} [Field k] [Field L] [Algebra k L]
    [Algebra.IsGeometricallyReduced k L] [Finite ι]
    (p : ℕ) (hp : p.Prime) [ExpChar k p] [ExpChar L p]
    {b : ι → k} (hb : LinearIndependent (frobenius k p).fieldRange b) :
    LinearIndependent (frobenius L p).fieldRange
      (fun i => algebraMap k L (b i)) := by
  classical
  let := Fintype.ofFinite ι
  let A := AlgebraicClosure k
  let D := L ⊗[k] A
  let : ExpChar A p := expChar_of_injective_algebraMap
    (RingHom.injective (algebraMap k A)) p
  let : IsReduced (A ⊗[k] L) :=
    (Algebra.isGeometricallyReduced_field_iff k L).mp inferInstance
  let : IsReduced D := isReduced_of_injective
    (Algebra.TensorProduct.comm k L A) (Algebra.TensorProduct.comm k L A).injective
  let : ExpChar D p := expChar_of_injective_ringHom
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k)
      (A := L) (B := A) (RingHom.injective (algebraMap k A))) p
  choose d hd using fun i =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap k A (b i)) hp.pos
  have hdLI : LinearIndependent k d := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hcA : ∑ i, algebraMap k A (c i ^ p * b i) = 0 := by
      have hs : (∑ i, algebraMap k A (c i) * d i) ^ p =
          ∑ i, (algebraMap k A (c i)) ^ p * d i ^ p := by
        simpa only [mul_pow] using
          (sum_pow_char p Finset.univ (fun i => algebraMap k A (c i) * d i))
      have hc' : ∑ i, algebraMap k A (c i) * d i = 0 := by
        simpa only [Algebra.smul_def] using hc
      rw [hc', zero_pow hp.ne_zero] at hs
      simpa only [← map_pow, hd, ← map_mul] using hs.symm
    have hck : ∑ i, c i ^ p * b i = 0 := by
      apply (algebraMap k A).injective
      simpa only [map_sum, map_zero] using hcA
    let cp : ι → (frobenius k p).fieldRange :=
      fun i => (frobenius k p).rangeRestrictField (c i)
    have hc0 : ∀ i, cp i = 0 := Fintype.linearIndependent_iff.mp hb cp (by
      change ∑ i, c i ^ p * b i = 0
      exact hck)
    intro i
    have hh : c i ^ p = 0 := congrArg Subtype.val (hc0 i)
    exact eq_zero_of_pow_eq_zero hh
  have ht : LinearIndependent L (fun i => (1 : L) ⊗ₜ[k] d i) :=
    Module.Flat.linearIndependent_one_tmul hdLI
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hcroot (i : ι) : ∃ z : L, z ^ p = (c i : L) := by
    have hh := (c i).property
    change ∃ z : L, frobenius L p z = (c i : L) at hh
    simpa only [frobenius_def] using hh
  choose z hz using hcroot
  have hcz : ∑ i, z i ^ p * algebraMap k L (b i) = 0 := by
    change ∑ i, (c i : L) * algebraMap k L (b i) = 0 at hc
    simpa only [hz] using hc
  have hpow : (∑ i, z i ⊗ₜ[k] d i : D) ^ p = 0 := by
    calc
      _ = ∑ i, (z i ^ p) ⊗ₜ[k] (d i ^ p) := by
        simpa only [Algebra.TensorProduct.tmul_pow] using
          (sum_pow_char p Finset.univ (fun i => (z i ⊗ₜ[k] d i : D)))
      _ = (∑ i, z i ^ p * algebraMap k L (b i)) ⊗ₜ[k] (1 : A) := by
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hd]
        rw [show algebraMap k A (b i) = b i • (1 : A) by
          simp only [Algebra.smul_def, mul_one]]
        rw [← TensorProduct.smul_tmul]
        simp only [Algebra.smul_def, mul_comm]
      _ = 0 := by rw [hcz, TensorProduct.zero_tmul]
  have hzero : (∑ i, z i ⊗ₜ[k] d i : D) = 0 := eq_zero_of_pow_eq_zero hpow
  have hz0 : ∀ i, z i = 0 := Fintype.linearIndependent_iff.mp ht z (by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hzero)
  intro i
  apply Subtype.ext
  change (c i : L) = 0
  rw [← hz i, hz0 i, zero_pow hp.ne_zero]

end Algebra
