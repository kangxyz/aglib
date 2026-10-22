/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Boundary separation on saturated blowup charts

The local algebra in Conrad, *Deligne's notes on Nagata compactifications*,
Lemma 1.5, https://virtualmath1.stanford.edu/~conrad/papers/nagatafinal.pdf.
The square of the first ideal is essential. A chart of the blowup
of `I₁ ⊔ I₂`, indexed by `s₂ ∈ I₂`, divides one factor of `I₁²` by `s₂`.
The resulting function lies in the extended `I₁` and equals one on the
closure of the localized closed subscheme.

All rings may be nonreduced, and the map out of the chart may be nonflat.
This is the local chart theorem, not the global separation lemma: covering
the protected boundary by these charts and comparing the relevant schematic
image with the localized closed subscheme remain geometric obligations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Dividing one factor of a square ideal produces the separating function.
No cancellation by `s` in the ambient ring is used. -/
lemma exists_separator_of_mem_sq_sup (I J : Ideal R) (s : R)
    (hI : I ≤ Ideal.span {s}) (hs : s ∈ I ^ 2 ⊔ J) :
    ∃ h ∈ I, s * (1 - h) ∈ J := by
  obtain ⟨t, ht, g, hg, htg⟩ := Submodule.mem_sup.mp hs
  have ht' : t ∈ I * Ideal.span {s} := by
    apply (Ideal.mul_mono_right hI)
    simpa only [pow_two] using ht
  obtain ⟨h, hh, he⟩ := Ideal.mem_mul_span_singleton.mp ht'
  refine ⟨h, hh, ?_⟩
  have hsep : s * (1 - h) = g := by
    calc
      s * (1 - h) = s - t := by rw [← he]; ring
      _ = g := by rw [← htg]; ring
  rwa [hsep]

/-- The separating function makes the boundary ideal comaximal with the
contraction of the extended closure ideal wherever the denominator is a unit. -/
lemma sup_comap_map_eq_top_of_mem_sq_sup {D : Type v} [CommRing D]
    (I J : Ideal R) (s : R) (e : R →+* D)
    (hI : I ≤ Ideal.span {s}) (hs : s ∈ I ^ 2 ⊔ J)
    (hu : IsUnit (e s)) : I ⊔ (J.map e).comap e = ⊤ := by
  obtain ⟨h, hh, hsep⟩ := exists_separator_of_mem_sq_sup I J s hI hs
  have hloc : e (1 - h) ∈ J.map e := by
    apply (Ideal.unit_mul_mem_iff_mem (J.map e) hu).mp
    rw [← map_mul]
    exact Ideal.mem_map_of_mem e hsep
  rw [Ideal.eq_top_iff_one]
  have hh' : h ∈ I ⊔ (J.map e).comap e :=
    (show I ≤ I ⊔ (J.map e).comap e from le_sup_left) hh
  have hloc' : 1 - h ∈ I ⊔ (J.map e).comap e :=
    (show (J.map e).comap e ≤ I ⊔ (J.map e).comap e from le_sup_right) hloc
  convert (I ⊔ (J.map e).comap e).add_mem hh' hloc' using 1; ring

/-- An affine support containment can be upgraded to scheme-theoretic
containment by a positive power of a finitely generated source ideal.
The target ring need not be Noetherian. -/
lemma exists_pos_pow_map_le_of_le_radical {S : Type v} [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (hI : I.FG)
    (h : I.map f ≤ J.radical) :
    ∃ n : ℕ, 0 < n ∧ (I ^ n).map f ≤ J := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h (hI.map f)
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  rw [Ideal.map_pow]
  exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn

end Ideal

namespace Localization.Away

variable {A : Type u} [CommRing A] {C : Type v} [CommRing C] [Algebra A C]

/-- On any algebra over the actual saturated `s`-chart, the image of the
centre is divisible by the image of `s`, using the literal fractions `b/s`. -/
lemma map_le_span_denominator (I : Ideal A) (s : A)
    (φ : saturatedChart A I s →ₐ[A] C) :
    I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C s} := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  apply Ideal.mem_span_singleton.mpr
  let q : saturatedChart A I s := ⟨fraction s b, fraction_mem I s b hb⟩
  refine ⟨φ q, ?_⟩
  have hq : q * algebraMap A (saturatedChart A I s) s =
      algebraMap A (saturatedChart A I s) b := by
    apply Subtype.ext
    exact fraction_mul_self s b
  have h := congrArg φ hq
  simpa only [map_mul, AlgHom.commutes, mul_comm] using h.symm

/-- Exact local algebra of Conrad's boundary separation: the schematic
containment uses `I₁²`, and the blowup centre is `I₁ ⊔ I₂`, not `I₁² ⊔ I₂`.
The algebra `C` can be an arbitrary base change of the chart. -/
lemma boundary_sup_localizedClosure_eq_top (I₁ I₂ : Ideal A) (s₂ : A)
    (hs₂ : s₂ ∈ I₂) (φ : saturatedChart A (I₁ ⊔ I₂) s₂ →ₐ[A] C)
    (J : Ideal C)
    (hcontain : I₂.map (algebraMap A C) ≤ (I₁ ^ 2).map (algebraMap A C) ⊔ J) :
    I₁.map (algebraMap A C) ⊔
      (J.map (algebraMap C (Localization.Away (algebraMap A C s₂)))).comap
        (algebraMap C (Localization.Away (algebraMap A C s₂))) = ⊤ := by
  apply Ideal.sup_comap_map_eq_top_of_mem_sq_sup
    (I₁.map (algebraMap A C)) J (algebraMap A C s₂)
  · exact (Ideal.map_mono le_sup_left).trans (map_le_span_denominator _ _ φ)
  · simpa only [Ideal.map_pow] using hcontain (Ideal.mem_map_of_mem _ hs₂)
  · exact IsLocalization.Away.algebraMap_isUnit (algebraMap A C s₂)

/-- The closure of the localized closed subscheme is genuinely disjoint from
the pulled-back first boundary. This uses the native spectrum-closure theorem,
not a set-theoretic replacement for the schematic-containment hypothesis. -/
lemma boundary_inter_closure_localized_zeroLocus_eq_empty
    (I₁ I₂ : Ideal A) (s₂ : A) (hs₂ : s₂ ∈ I₂)
    (φ : saturatedChart A (I₁ ⊔ I₂) s₂ →ₐ[A] C) (J : Ideal C)
    (hcontain : I₂.map (algebraMap A C) ≤ (I₁ ^ 2).map (algebraMap A C) ⊔ J) :
    PrimeSpectrum.zeroLocus (I₁.map (algebraMap A C) : Set C) ∩
      closure (PrimeSpectrum.comap
        (algebraMap C (Localization.Away (algebraMap A C s₂))) ''
        PrimeSpectrum.zeroLocus
          (J.map (algebraMap C (Localization.Away (algebraMap A C s₂))) :
            Set (Localization.Away (algebraMap A C s₂)))) = ∅ := by
  rw [PrimeSpectrum.closure_image_comap_zeroLocus,
    ← PrimeSpectrum.zeroLocus_sup,
    boundary_sup_localizedClosure_eq_top I₁ I₂ s₂ hs₂ φ J hcontain]
  exact PrimeSpectrum.zeroLocus_univ

end Localization.Away
