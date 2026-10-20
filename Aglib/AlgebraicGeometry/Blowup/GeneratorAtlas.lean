/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `127e905eade5bb7beaaca518cd26c06fc46b8726523e38120ecb7c6f4abbc2be`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Generator subcovers of an affine blowup atlas

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.Blowup.AffineAtlas


/-!
# Generator subcovers of the saturated affine blowup atlas

Conditional only on the precise ordinary `AffineAtlas` object. The subcover
condition is proved from ideal generation; it is not a new premise. In fact
this argument works for an arbitrary generating family, and hence also a
finite one. No existence family is instantiated in this file.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Blowup
universe v
namespace AlgebraicGeometry.Scheme.Blowup.AffineAtlas
variable {A : Type u} [CommRing A] {I : Ideal A}

@[simp] theorem ratio_self (a : I) : ratio A I a a = 1 := by
  apply Subtype.ext
  exact IsLocalization.Away.mul_invSelf (a : A)

/-- The ratios of any actual generating family generate the unit ideal on
any saturated chart, including charts with a zero denominator. -/
theorem ratio_span_eq_top {ι : Type v} (g : ι → I)
    (hg : Ideal.span (Set.range fun i => (g i : A)) = I) (a : I) :
    Ideal.span (Set.range fun i => ratio A I a (g i)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (x := 1) ?_ isUnit_one
  let J := Ideal.span (Set.range fun i => ratio A I a (g i))
  have key : ∀ b ∈ Ideal.span (Set.range fun i => (g i : A)),
      ∀ hb : b ∈ I, ratio A I a ⟨b, hb⟩ ∈ J := by
    intro b hspan
    induction hspan using Submodule.span_induction with
    | mem b hb =>
      intro hbI
      obtain ⟨i, rfl⟩ := hb
      exact Ideal.subset_span ⟨i, rfl⟩
    | zero =>
      intro hbI
      have h : ratio A I a ⟨0, hbI⟩ = 0 := by
        apply Subtype.ext; simp [ratio]
      simpa only [h] using J.zero_mem
    | add b c hb hc ihb ihc =>
      intro hbI
      have hb' : b ∈ I := by exact hg.le hb
      have hc' : c ∈ I := by exact hg.le hc
      have h : ratio A I a ⟨b+c, hbI⟩ =
          ratio A I a ⟨b, hb'⟩ + ratio A I a ⟨c, hc'⟩ := by
        apply Subtype.ext; simp [ratio, add_mul]
      simpa only [h] using J.add_mem (ihb hb') (ihc hc')
    | smul r b hb ih =>
      intro hbI
      have hb' : b ∈ I := by exact hg.le hb
      have h : ratio A I a ⟨r • b, hbI⟩ =
          algebraMap A (affineBlowupAlgebra A I a) r * ratio A I a ⟨b, hb'⟩ := by
        apply Subtype.ext; simp [ratio, smul_eq_mul, mul_assoc]
      simpa only [h] using J.mul_mem_left (algebraMap A _ r) (ih hb')
  simpa using key a (by rw [hg]; exact a.property) a.property

/-- Every point of every chart lies in one generator-ratio principal open. -/
theorem exists_ratio_not_mem {ι : Type v} (g : ι → I)
    (hg : Ideal.span (Set.range fun i => (g i : A)) = I) (a : I)
    (x : PrimeSpectrum (affineBlowupAlgebra A I a)) :
    ∃ i, ratio A I a (g i) ∉ x.asIdeal := by
  by_contra! h
  have hle : Ideal.span (Set.range fun i => ratio A I a (g i)) ≤ x.asIdeal :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [ratio_span_eq_top g hg a] at hle
  exact x.isPrime.ne_top (top_unique hle)

/-- The specific canonical charts of the given ideal generators cover the
same actual blowup, derived via the literal overlap-range identity. -/
theorem generator_covers {ι : Type v} (g : ι → I)
    (hg : Ideal.span (Set.range fun i => (g i : A)) = I)
    {B : BlowupDatum (affineCenter A I)} (H : AffineAtlas A I B) :
    ∀ y : B.Y, ∃ i, y ∈ Set.range (H.chart (g i)) := by
  intro y
  obtain ⟨a, x, rfl⟩ := H.covers y
  obtain ⟨i, hi⟩ := exists_ratio_not_mem g hg a x
  have hx : x ∈ Set.range (affineOverlapMap A I a (g i)) := by
    change x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (affineBlowupAlgebra A I a)
        (Localization.Away (ratio A I a (g i)))))
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (ratio A I a (g i))) (ratio A I a (g i))]
    exact hi
  obtain ⟨z, hz⟩ := hx
  refine ⟨i, ?_⟩
  have hr : H.chart a x ∈ Set.range (affineOverlapMap A I a (g i) ≫ H.chart a) :=
    ⟨z, by change H.chart a (affineOverlapMap A I a (g i) z) = H.chart a x; rw [hz]⟩
  rw [H.overlap] at hr
  exact hr.2

end AlgebraicGeometry.Scheme.Blowup.AffineAtlas

end
end AlgebraicGeometry.Scheme.Blowup.AffineAtlas
