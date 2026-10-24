/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finite constant roots for a purely inseparable rational extension

The rational field is supplied by its actual numerator and denominator
presentation in an ambient algebraically closed field. Thus the result applies
directly to the fraction field of a polynomial ring, without changing its
coefficient action. Only the coefficients used by a finite basis are adjoined.
-/

@[expose] public noncomputable section

open Polynomial

namespace IsPurelyInseparable

private theorem eval₂_mem_intermediateField
    {K Ω : Type*} [Field K] [Field Ω] {E : Type*} [Field E] [Algebra E Ω]
    (S : IntermediateField E Ω) (f : K →+* Ω) (z : Ω) (a : K[X])
    (hz : z ∈ S) (ha : ∀ n ∈ a.support, f (a.coeff n) ∈ S) :
    a.eval₂ f z ∈ S := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  exact S.sum_mem fun n hn => S.mul_mem (ha n hn) (S.toSubalgebra.pow_mem hz n)

private theorem eval₂_root_pow
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (p e : ℕ) [ExpChar Ω p] (f : K →+* Ω)
    (hf : ∀ c, f c ^ p ^ e = algebraMap K Ω c) (z : Ω) (a : K[X]) :
    a.eval₂ f z ^ p ^ e = aeval (z ^ p ^ e) a := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb =>
    simpa only [Polynomial.eval₂_add, map_add, add_pow_expChar_pow] using
      congrArg₂ (· + ·) ha hb
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial, Polynomial.aeval_monomial,
      mul_pow, hf, ← pow_mul, Nat.mul_comm n (p ^ e)]

/-- A finite purely inseparable extension of an actual rational field is
contained in `E(z)`, where `E` is a finite purely inseparable extension of
the constant field inside the supplied algebraically closed ambient field
and `z` is a root of a single characteristic power of the original variable.

The rational-generation hypothesis uses the supplied map `F → Ω`. In the
polynomial Japanese application, `F` is the literal fraction field of the
original polynomial ring and this hypothesis is its fraction presentation. -/
theorem exists_finite_constant_field
    (K F L Ω : Type*) [Field K] [Field F] [Field L] [Field Ω]
    [Algebra K Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsAlgClosed Ω]
    [FiniteDimensional F L] [IsPurelyInseparable F L]
    (p : ℕ) [ExpChar K p] [ExpChar F p]
    (t : Ω) (ht : Transcendental K t)
    (hF : ∀ x : F, ∃ a b : K[X],
      algebraMap F Ω x = aeval t a / aeval t b) :
    ∃ (E : IntermediateField K Ω) (e : ℕ) (z : Ω),
      FiniteDimensional K E ∧ IsPurelyInseparable K E ∧
      z ^ p ^ e = t ∧ Transcendental E z ∧
      ∀ x : L, algebraMap L Ω x ∈ IntermediateField.adjoin E {z} := by
  classical
  let : ExpChar Ω p :=
    expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  let e := exponent F L
  let ρ : Ω ≃+* Ω := (iterateFrobeniusEquiv Ω p e).symm
  let root : K →+* Ω := ρ.toRingHom.comp (algebraMap K Ω)
  have hroot (c : K) : root c ^ p ^ e = algebraMap K Ω c :=
    (iterateFrobeniusEquiv Ω p e).apply_symm_apply _
  let z := ρ t
  have hz : z ^ p ^ e = t :=
    (iterateFrobeniusEquiv Ω p e).apply_symm_apply t
  let b := Module.finBasis F L
  choose a d had using fun i =>
    hF (IsPurelyInseparable.iterateFrobenius F L p (le_refl e) (b i))
  let s : Finset K := Finset.univ.biUnion fun i =>
    (a i).support.image (a i).coeff ∪ (d i).support.image (d i).coeff
  let E := IntermediateField.adjoin K (↑(s.image root) : Set Ω)
  have hroot_mem (c : K) (hc : c ∈ s) : root c ∈ E :=
    IntermediateField.subset_adjoin K _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have hfinite : FiniteDimensional K E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    apply isAlgebraic_iff_isIntegral.mp
    apply IsAlgebraic.of_pow (expChar_pow_pos K p e)
    rw [hroot]
    exact isAlgebraic_algebraMap c
  have hpure : IsPurelyInseparable K E := by
    apply (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem K Ω p).mpr
    rintro x hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨e, c, (hroot c).symm⟩
  let : FiniteDimensional K E := hfinite
  have hztr : Transcendental E z := by
    apply (Algebra.IsAlgebraic.transcendental_iff K E).mp
    intro halg
    exact ht (hz ▸ halg.pow (p ^ e))
  let S := IntermediateField.adjoin E {z}
  have hzS : z ∈ S := IntermediateField.subset_adjoin E _ (by simp)
  have hKS (c : K) : algebraMap K Ω c ∈ S := by
    rw [IsScalarTower.algebraMap_apply K E Ω]
    exact S.algebraMap_mem _
  have hFS (x : F) : algebraMap F Ω x ∈ S := by
    obtain ⟨f, g, hfg⟩ := hF x
    rw [hfg]
    apply S.div_mem
    · exact eval₂_mem_intermediateField S (algebraMap K Ω) t f
        (hz ▸ S.toSubalgebra.pow_mem hzS (p ^ e)) (fun n _ => hKS (f.coeff n))
    · exact eval₂_mem_intermediateField S (algebraMap K Ω) t g
        (hz ▸ S.toSubalgebra.pow_mem hzS (p ^ e)) (fun n _ => hKS (g.coeff n))
  have haS (i) : (a i).eval₂ root z ∈ S := by
    apply eval₂_mem_intermediateField S root z (a i) hzS
    intro n hn
    have hc : root ((a i).coeff n) ∈ E := hroot_mem _ <|
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)⟩
    exact S.algebraMap_mem ⟨_, hc⟩
  have hdS (i) : (d i).eval₂ root z ∈ S := by
    apply eval₂_mem_intermediateField S root z (d i) hzS
    intro n hn
    have hc : root ((d i).coeff n) ∈ E := hroot_mem _ <|
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)⟩
    exact S.algebraMap_mem ⟨_, hc⟩
  have hbS (i) : algebraMap L Ω (b i) ∈ S := by
    have heq : algebraMap L Ω (b i) =
        (a i).eval₂ root z / (d i).eval₂ root z := by
      apply (_root_.iterateFrobenius Ω p e).injective
      change algebraMap L Ω (b i) ^ p ^ e =
        ((a i).eval₂ root z / (d i).eval₂ root z) ^ p ^ e
      rw [div_pow, eval₂_root_pow p e root hroot,
        eval₂_root_pow p e root hroot, hz]
      rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p
        (le_refl e), ← IsScalarTower.algebraMap_apply F L Ω]
      exact had i
    rw [heq]
    exact S.div_mem (haS i) (hdS i)
  refine ⟨E, e, z, hfinite, hpure, hz, hztr, ?_⟩
  intro x
  rw [← b.sum_repr x, map_sum]
  apply S.sum_mem
  intro i _
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply F L Ω]
  exact S.mul_mem (hFS _) (hbS i)

end IsPurelyInseparable
