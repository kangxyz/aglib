/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Weak transforms in the actual saturated blowup chart

The ideal is the colon of the extended ideal by a specified power of the actual
exceptional parameter. If `J ≤ I ^ r`, multiplication by that power recovers
the extended ideal. The parameter acts injectively because the chart is the
original subalgebra of `A[1/a]`. No domain assumption is needed for these facts.

For the weak transform at the order of an ideal, the caller takes `I` to be the
actual maximal ideal and `r` to be its actual order. Existence of that order,
finite support and the strict colength decrease are separate assertions.
-/

@[expose] public section

noncomputable section

universe u v

namespace Localization.Away

variable {A : Type u} [CommRing A] (I J : Ideal A) (a : A) (r : ℕ)

/-- The original centre ideal becomes the principal exceptional ideal in its
literal saturated chart. -/
theorem map_center_eq_span (ha : a ∈ I) :
    I.map (algebraMap A (saturatedChart A I a)) =
      Ideal.span {algebraMap A (saturatedChart A I a) a} := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change algebraMap A (saturatedChart A I a) b ∈
      Ideal.span {algebraMap A (saturatedChart A I a) a}
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨fraction a b, fraction_mem I a b hb⟩, ?_⟩
    apply Subtype.ext
    change algebraMap A (Localization.Away a) b =
      algebraMap A (Localization.Away a) a * fraction a b
    simpa only [mul_comm] using (fraction_mul_self a b).symm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mem_map_of_mem _ ha

/-- Powers of the centre become powers of the actual exceptional parameter. -/
theorem map_center_pow_eq_span (ha : a ∈ I) :
    (I ^ r).map (algebraMap A (saturatedChart A I a)) =
      Ideal.span {(algebraMap A (saturatedChart A I a) a) ^ r} := by
  rw [Ideal.map_pow, map_center_eq_span I a ha, Ideal.span_singleton_pow]

/-- Dividing the actual extended ideal by a specified exceptional power. -/
def weakTransform : Ideal (saturatedChart A I a) :=
  (J.map (algebraMap A (saturatedChart A I a))).colon
    {(algebraMap A (saturatedChart A I a) a) ^ r}

@[simp]
theorem mem_weakTransform {x : saturatedChart A I a} :
    x ∈ weakTransform I J a r ↔
      (algebraMap A (saturatedChart A I a) a) ^ r * x ∈
        J.map (algebraMap A (saturatedChart A I a)) := by
  simp only [weakTransform, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]

/-- The actual division recovers the extended ideal, not merely its radical. -/
theorem exceptional_pow_mul_weakTransform (ha : a ∈ I) (hJ : J ≤ I ^ r) :
    Ideal.span {(algebraMap A (saturatedChart A I a) a) ^ r} *
        weakTransform I J a r =
      J.map (algebraMap A (saturatedChart A I a)) := by
  apply le_antisymm
  · apply Ideal.span_singleton_mul_le_iff.mpr
    intro x hx
    exact (mem_weakTransform I J a r).mp hx
  · intro x hx
    have hx' : x ∈ Ideal.span {(algebraMap A (saturatedChart A I a) a) ^ r} := by
      rw [← map_center_pow_eq_span I a r ha]
      exact Ideal.map_mono hJ hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx'
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨y, (mem_weakTransform I J a r).mpr ?_, hy.symm⟩
    rwa [← hy]

/-- Exceptional powers act injectively in the saturated chart, including when
the original ring has zero divisors. -/
theorem exceptional_pow_mul_injective :
    Function.Injective (fun x : saturatedChart A I a =>
      (algebraMap A (saturatedChart A I a) a) ^ r * x) := by
  intro x y h
  apply Subtype.ext
  apply ((IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away a) a).pow r).mul_left_injective
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
    mul_comm] using
    congrArg (fun z : saturatedChart A I a => (z : Localization.Away a)) h

/-- The factor ideal in the actual exceptional-power factorization is unique. -/
theorem eq_weakTransform_of_exceptional_pow_mul
    (K : Ideal (saturatedChart A I a))
    (hK : Ideal.span {(algebraMap A (saturatedChart A I a) a) ^ r} * K =
      J.map (algebraMap A (saturatedChart A I a))) :
    K = weakTransform I J a r := by
  apply le_antisymm
  · intro x hx
    apply (mem_weakTransform I J a r).mpr
    rw [← hK]
    exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
  · intro x hx
    have hm := (mem_weakTransform I J a r).mp hx
    rw [← hK] at hm
    obtain ⟨y, hy, hxy⟩ := Ideal.mem_span_singleton_mul.mp hm
    have h : y = x := exceptional_pow_mul_injective I a r hxy
    exact h ▸ hy

/-- The transform is the unit ideal exactly when the exceptional power itself
belongs to the original extended ideal. -/
theorem weakTransform_eq_top_iff :
    weakTransform I J a r = ⊤ ↔
      (algebraMap A (saturatedChart A I a) a) ^ r ∈
        J.map (algebraMap A (saturatedChart A I a)) := by
  rw [Ideal.eq_top_iff_one, mem_weakTransform]
  simp only [mul_one]

/-- A power of the exceptional parameter kills the quotient by the transform
whenever a power of the centre is contained in the original ideal. -/
theorem exceptional_pow_mem_weakTransform (ha : a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) (hr : r ≤ N) :
    (algebraMap A (saturatedChart A I a) a) ^ (N - r) ∈
      weakTransform I J a r := by
  apply (mem_weakTransform I J a r).mpr
  rw [← pow_add, Nat.add_sub_of_le hr, ← map_pow]
  exact Ideal.mem_map_of_mem _ (hN (Ideal.pow_mem_pow ha N))

/-- The same genuine factorization survives any ring map out of the chart,
in particular the localization map to an actual exceptional-point local ring. -/
theorem map_exceptional_pow_mul_weakTransform
    {B : Type v} [CommRing B] (f : saturatedChart A I a →+* B)
    (ha : a ∈ I) (hJ : J ≤ I ^ r) :
    Ideal.span {(f (algebraMap A (saturatedChart A I a) a)) ^ r} *
        (weakTransform I J a r).map f =
      J.map (f.comp (algebraMap A (saturatedChart A I a))) := by
  have h := congrArg (Ideal.map f) (exceptional_pow_mul_weakTransform I J a r ha hJ)
  simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow,
    Ideal.map_map] using h

/-- After a chart map preserving regularity of the exceptional parameter, the
extended transform is the actual colon ideal in the target ring. This applies
to its local rings with their regular exceptional parameter. -/
theorem map_weakTransform_eq_colon
    {B : Type v} [CommRing B] (f : saturatedChart A I a →+* B)
    (ha : a ∈ I) (hJ : J ≤ I ^ r)
    (hreg : IsRegular (f (algebraMap A (saturatedChart A I a) a))) :
    (weakTransform I J a r).map f =
      (J.map (f.comp (algebraMap A (saturatedChart A I a)))).colon
        {(f (algebraMap A (saturatedChart A I a) a)) ^ r} := by
  have hfac := map_exceptional_pow_mul_weakTransform I J a r f ha hJ
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_colon_singleton.mpr
    change x * (f (algebraMap A (saturatedChart A I a) a)) ^ r ∈ _
    rw [← hfac]
    exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, mul_comm _ _⟩
  · intro x hx
    have hm : (f (algebraMap A (saturatedChart A I a) a)) ^ r * x ∈
        J.map (f.comp (algebraMap A (saturatedChart A I a))) := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx
    rw [← hfac] at hm
    obtain ⟨y, hy, hxy⟩ := Ideal.mem_span_singleton_mul.mp hm
    have h : y = x := (hreg.pow r).left hxy
    exact h ▸ hy

end Localization.Away
