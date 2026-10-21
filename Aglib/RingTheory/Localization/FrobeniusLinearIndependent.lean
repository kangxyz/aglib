/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Frobenius independence under passage to fraction fields

Native common denominators and fraction-field linear-independence transport
preserve a finite Frobenius independence supplier over its original base.
-/

@[expose] public noncomputable section

namespace IsFractionRing

/-- Transfer finite Frobenius independence from a domain algebra to its fraction field.
The fraction-field action on the target must be the supplied compatible action. -/
lemma linearIndependent_pow_of_domain
    {R S F L ι : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Field F] [Field L] [Algebra R S] [Algebra R F] [IsFractionRing R F]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
    [Algebra F L] [IsScalarTower R F L] [Finite ι]
    (p : ℕ)
    (H : ∀ f : ι → S, LinearIndependent R f → LinearIndependent R (fun i => f i ^ p))
    (v : ι → L) (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => v i ^ p) := by
  classical
  let := Fintype.ofFinite ι
  have hvR : LinearIndependent R v := (LinearIndependent.iff_fractionRing R F).mpr hv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors S) v
  choose f hf using hb
  have hb0 : algebraMap S L (b : S) ≠ 0 := by
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp b.property
    apply IsFractionRing.injective S L
    simpa only [map_zero] using h
  let l : S →ₗ[R] L := (IsScalarTower.toAlgHom R S L).toLinearMap
  have hfR : LinearIndependent R f := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hcL : ∑ i, c i • algebraMap S L (f i) = 0 := by
      have h := congrArg l hc
      rw [map_sum, map_zero] at h
      simp only [map_smul] at h
      exact h
    have hz : algebraMap S L (b : S) * (∑ i, c i • v i) = 0 := by
      rw [Finset.mul_sum]
      have hsum :
          (∑ i, algebraMap S L (b : S) * (c i • v i)) =
          ∑ i, c i • algebraMap S L (f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hf i]
        simp only [Algebra.smul_def]
        ring
      exact hsum.trans hcL
    exact Fintype.linearIndependent_iff.mp hvR c ((mul_eq_zero.mp hz).resolve_left hb0)
  have hfpR := H f hfR
  have hfpL : LinearIndependent R (fun i => algebraMap S L (f i ^ p)) :=
    hfpR.map' l (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective S L))
  apply (LinearIndependent.iff_fractionRing R F).mp
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp hfpL c
  calc
    ∑ i, c i • algebraMap S L (f i ^ p) =
        (algebraMap S L (b : S)) ^ p * (∑ i, c i • v i ^ p) := by
      simp only [map_pow, hf, Algebra.smul_def, mul_pow, mul_left_comm, Finset.mul_sum]
    _ = 0 := by rw [hc, mul_zero]

end IsFractionRing
