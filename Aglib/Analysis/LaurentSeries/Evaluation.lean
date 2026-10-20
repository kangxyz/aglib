/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.LaurentSeries.AllRadii
public import Mathlib.Tactic.FieldSimp

/-!
# Evaluation of fractions on the actual regular subring

Source: `R5Lab.Aglib.Analysis.LaurentSeries.Evaluation`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
namespace LaurentSeries.AllRadii
universe u v
variable {F : Type u} [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
variable {K : Type v} [NormedField K] [CompleteSpace K]
variable (f : F →+* K) [RingHomIsometric f]

/-- Honest partial evaluation: a fraction can be evaluated only through a presentation
whose actual Laurent denominator has nonzero value. There is no total field evaluation. -/
def EvaluatesAt (u : Kˣ) (m : Meromorphic F) (z : K) : Prop :=
  ∃ a b : Series F,
    Series.evaluationHom f u b ≠ 0 ∧
    m = algebraMap (Series F) (Meromorphic F) a / algebraMap (Series F) (Meromorphic F) b ∧
    z = Series.evaluationHom f u a / Series.evaluationHom f u b

omit [IsUltrametricDist F] in
/-- A nonzero denominator value entails a nonzero actual Laurent denominator. -/
@[nolint unusedArguments]
theorem series_ne_zero_of_evaluation_ne_zero [IsUltrametricDist F] (u : Kˣ) {b : Series F}
    (hb : Series.evaluationHom f u b ≠ 0) : b ≠ 0 := by
  intro h
  exact hb (by rw [h, map_zero])

/-- Partial evaluation is independent of every qualifying fraction presentation. -/
theorem EvaluatesAt.unique (u : Kˣ) {m : Meromorphic F} {z z' : K}
    (hz : EvaluatesAt f u m z) (hz' : EvaluatesAt f u m z') : z = z' := by
  obtain ⟨a, b, hb, hm, rfl⟩ := hz
  obtain ⟨a', b', hb', hm', rfl⟩ := hz'
  have hd : algebraMap (Series F) (Meromorphic F) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Series F) (Meromorphic F))).mpr
      (series_ne_zero_of_evaluation_ne_zero f u hb)
  have hd' : algebraMap (Series F) (Meromorphic F) b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Series F) (Meromorphic F))).mpr
      (series_ne_zero_of_evaluation_ne_zero f u hb')
  have hcross := (div_eq_div_iff hd hd').mp (hm.symm.trans hm')
  have hcoeff : a * b' = a' * b := by
    apply IsFractionRing.injective (Series F) (Meromorphic F)
    simpa only [map_mul] using hcross
  apply (div_eq_div_iff hb hb').mpr
  simpa only [map_mul] using congrArg (Series.evaluationHom f u) hcoeff

/-- Every Laurent series has its usual convergent evaluation. -/
theorem evaluatesAt_algebraMap (u : Kˣ) (a : Series F) :
    EvaluatesAt f u (algebraMap (Series F) (Meromorphic F) a) (Series.evaluationHom f u a) := by
  refine ⟨a, 1, by simp, by simp, by simp⟩

/-- Addition of regular presentations remains regular and respects values. -/
theorem EvaluatesAt.add (u : Kˣ) {m n : Meromorphic F} {z w : K}
    (hm : EvaluatesAt f u m z) (hn : EvaluatesAt f u n w) :
    EvaluatesAt f u (m + n) (z + w) := by
  obtain ⟨a, b, hb, rfl, rfl⟩ := hm
  obtain ⟨c, d, hd, rfl, rfl⟩ := hn
  have hb0 := series_ne_zero_of_evaluation_ne_zero f u hb
  have hd0 := series_ne_zero_of_evaluation_ne_zero f u hd
  have hb1 : algebraMap (Series F) (Meromorphic F) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Series F) (Meromorphic F))).mpr hb0
  have hd1 : algebraMap (Series F) (Meromorphic F) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Series F) (Meromorphic F))).mpr hd0
  refine ⟨a * d + c * b, b * d, by simpa using mul_ne_zero hb hd, ?_, ?_⟩
  · simp only [map_mul, map_add]
    field_simp
  · simp only [map_mul, map_add]
    field_simp

/-- Multiplication of regular presentations remains regular and respects values. -/
theorem EvaluatesAt.mul (u : Kˣ) {m n : Meromorphic F} {z w : K}
    (hm : EvaluatesAt f u m z) (hn : EvaluatesAt f u n w) :
    EvaluatesAt f u (m * n) (z * w) := by
  obtain ⟨a, b, hb, rfl, rfl⟩ := hm
  obtain ⟨c, d, hd, rfl, rfl⟩ := hn
  refine ⟨a * c, b * d, by simpa using mul_ne_zero hb hd, ?_, ?_⟩
  · simp only [map_mul, div_mul_div_comm]
  · simp only [map_mul, div_mul_div_comm]

/-- Negation preserves a qualifying denominator. -/
theorem EvaluatesAt.neg (u : Kˣ) {m : Meromorphic F} {z : K}
    (hm : EvaluatesAt f u m z) : EvaluatesAt f u (-m) (-z) := by
  obtain ⟨a, b, hb, rfl, rfl⟩ := hm
  exact ⟨-a, b, hb, by simp [neg_div], by simp [neg_div]⟩

/-- The actual subring of meromorphic fractions that are regular at this evaluation point. -/
def regularAt (u : Kˣ) : Subring (Meromorphic F) where
  carrier := {m | ∃ z : K, EvaluatesAt f u m z}
  zero_mem' := ⟨0, by simpa using evaluatesAt_algebraMap f u (0 : Series F)⟩
  one_mem' := ⟨1, by simpa using evaluatesAt_algebraMap f u (1 : Series F)⟩
  add_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, hz.add f u hw⟩
  mul_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z * w, hz.mul f u hw⟩
  neg_mem' := by
    rintro a ⟨z, hz⟩
    exact ⟨-z, hz.neg f u⟩

/-- Only the regular subring, never the entire meromorphic field, has this evaluation hom. -/
def evaluationAt (u : Kˣ) : regularAt f u →+* K where
  toFun m := Classical.choose m.property
  map_zero' := by
    apply EvaluatesAt.unique f u (Classical.choose_spec (0 : regularAt f u).property)
    simpa using evaluatesAt_algebraMap f u (0 : Series F)
  map_one' := by
    apply EvaluatesAt.unique f u (Classical.choose_spec (1 : regularAt f u).property)
    simpa using evaluatesAt_algebraMap f u (1 : Series F)
  map_add' a b := by
    apply EvaluatesAt.unique f u (Classical.choose_spec (a + b).property)
    exact (Classical.choose_spec a.property).add f u (Classical.choose_spec b.property)
  map_mul' a b := by
    apply EvaluatesAt.unique f u (Classical.choose_spec (a * b).property)
    exact (Classical.choose_spec a.property).mul f u (Classical.choose_spec b.property)

/-- The local evaluation hom returns exactly every independently qualifying value. -/
theorem evaluationAt_eq (u : Kˣ) (m : regularAt f u) (z : K)
    (hz : EvaluatesAt f u m z) : evaluationAt f u m = z :=
  EvaluatesAt.unique f u (Classical.choose_spec m.property) hz

end LaurentSeries.AllRadii
