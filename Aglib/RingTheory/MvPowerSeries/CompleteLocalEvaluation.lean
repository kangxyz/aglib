/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.TruncIdeal
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Native formal-series evaluation in complete local rings

The original coefficient and parameter maps define native evaluation. Exact
maximal-ideal generation gives surjectivity; in dimension two, the native
nonzerodivisor dimension drop gives injectivity of the same map.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped nonZeroDivisors

namespace MvPowerSeries

section Evaluation

variable {σ k R : Type*} [Finite σ] [CommRing k]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

/-- Native evaluation at original maximal-ideal elements, with the source
coefficient ring discrete and the target in its actual maximal-ideal topology. -/
def completeLocalEval (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) : MvPowerSeries σ k →+* R := by
  let : UniformSpace k := ⊥
  let : WithIdeal R := ⟨maximalIdeal R⟩
  have hm : IsAdic (maximalIdeal R) := rfl
  have : CompleteSpace R := hm.isAdicComplete_iff.mp inferInstance |>.1
  have : T2Space R := hm.isAdicComplete_iff.mp inferInstance |>.2
  have heval : HasEval x := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
    · simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  exact eval₂Hom (φ := s) continuous_of_discreteTopology heval

@[simp]
theorem completeLocalEval_C (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) (c : k) :
    completeLocalEval s x hx (C c) = s c := by
  let : UniformSpace k := ⊥
  let : WithIdeal R := ⟨maximalIdeal R⟩
  have hm : IsAdic (maximalIdeal R) := rfl
  have : CompleteSpace R := hm.isAdicComplete_iff.mp inferInstance |>.1
  have : T2Space R := hm.isAdicComplete_iff.mp inferInstance |>.2
  unfold completeLocalEval
  rw [coe_eval₂Hom, eval₂_C]

@[simp]
theorem completeLocalEval_X (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) (i : σ) :
    completeLocalEval s x hx (X i) = x i := by
  let : UniformSpace k := ⊥
  let : WithIdeal R := ⟨maximalIdeal R⟩
  have hm : IsAdic (maximalIdeal R) := rfl
  have : CompleteSpace R := hm.isAdicComplete_iff.mp inferInstance |>.1
  have : T2Space R := hm.isAdicComplete_iff.mp inferInstance |>.2
  unfold completeLocalEval
  rw [coe_eval₂Hom, eval₂_X]

/-- This is exact ideal image, not equality of radicals. -/
theorem map_span_X_completeLocalEval (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) :
    (Ideal.span (Set.range (X : σ → MvPowerSeries σ k))).map
      (completeLocalEval s x hx) = Ideal.span (Set.range x) := by
  have hX : completeLocalEval s x hx ∘ (X : σ → MvPowerSeries σ k) = x :=
    funext (completeLocalEval_X s x hx)
  rw [Ideal.map_span, ← Set.range_comp, hX]

/-- Evaluation reduces to its original coefficient map on the actual residue ring. -/
theorem residue_completeLocalEval (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R) (f : MvPowerSeries σ k) :
    residue R (completeLocalEval s x hx f) = residue R (s (constantCoeff f)) := by
  have ht := sub_truncTotal_mem_span_X_pow 1 f
  rw [pow_one, truncTotal_one_eq_C_constantCoeff, MvPolynomial.coe_C] at ht
  have hmaple : (Ideal.span (Set.range (X : σ → MvPowerSeries σ k))).map
      (completeLocalEval s x hx) ≤ maximalIdeal R := by
    rw [map_span_X_completeLocalEval]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx i
  have hmem := hmaple (Ideal.mem_map_of_mem (completeLocalEval s x hx) ht)
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  simpa only [map_sub, completeLocalEval_C] using hmem

/-- Residue-surjective coefficients and literal maximal-ideal generators
make the original evaluation surjective. No target Noetherian hypothesis is used. -/
theorem completeLocalEval_surjective (s : k →+* R) (x : σ → R)
    (hx : ∀ i, x i ∈ maximalIdeal R)
    (hspan : Ideal.span (Set.range x) = maximalIdeal R)
    (hres : Function.Surjective ((residue R).comp s)) :
    Function.Surjective (completeLocalEval s x hx) := by
  let V : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range X)
  have hmap : V.map (completeLocalEval s x hx) = maximalIdeal R :=
    (map_span_X_completeLocalEval s x hx).trans hspan
  have : IsHausdorff (V.map (completeLocalEval s x hx)) R := by
    rw [hmap]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (completeLocalEval s x hx) (I := V)
  change Function.Surjective ((Ideal.Quotient.mk (V.map (completeLocalEval s x hx))).comp
    (completeLocalEval s x hx))
  rw [hmap]
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, hc⟩ := hres (residue R r)
  change residue R (s c) = residue R r at hc
  refine ⟨C c, ?_⟩
  change Ideal.Quotient.mk (maximalIdeal R) (completeLocalEval s x hx (C c)) =
    Ideal.Quotient.mk (maximalIdeal R) r
  rw [completeLocalEval_C, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply (residue_eq_zero_iff _).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hc

end Evaluation

section TwoVariables

variable (k : Type*) [Field k]

/-- Over a field, the actual maximal ideal is the variable ideal. -/
theorem maximalIdeal_eq_span_X :
    maximalIdeal (MvPowerSeries (Fin 2) k) =
      Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) k)) := by
  apply le_antisymm
  · have hC (c : k) (hc : c ∈ maximalIdeal k) :
        (RingHom.id (MvPowerSeries (Fin 2) k)) (C c) ∈
          Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) k)) := by
      have hc0 : c = 0 := by simpa only [maximalIdeal_eq_bot, Ideal.mem_bot] using hc
      change C c ∈ _
      rw [hc0, map_zero]
      exact Ideal.zero_mem _
    have hX (i : Fin 2) :
        (RingHom.id (MvPowerSeries (Fin 2) k)) (X i) ∈
          Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) k)) :=
      Ideal.subset_span ⟨i, rfl⟩
    simpa only [Ideal.comap_id] using
      (maximalIdeal_le_comap_of_C_X (σ := Fin 2) (R := k)
        (RingHom.id (MvPowerSeries (Fin 2) k)) _ hC hX)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]

/-- The upper dimension bound suffices: no separate series regularity or
complete-local classification theorem is needed. -/
theorem ringKrullDim_twoVariable_le : ringKrullDim (MvPowerSeries (Fin 2) k) ≤ 2 := by
  have hrange : Set.range (X : Fin 2 → MvPowerSeries (Fin 2) k) =
      ({X 0, X 1} : Set (MvPowerSeries (Fin 2) k)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hbound : (maximalIdeal (MvPowerSeries (Fin 2) k)).spanFinrank ≤ 2 := by
    rw [maximalIdeal_eq_span_X, hrange]
    apply (Submodule.spanFinrank_span_le_ncard_of_finite
      ((Set.finite_singleton (X (R := k) (1 : Fin 2))).insert (X 0))).trans
    simpa only [Set.ncard_singleton] using
      Set.ncard_insert_le (X (R := k) (0 : Fin 2)) ({X 1} : Set _)
  exact (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hbound)

variable {k} {R : Type*} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- In dimension two, the surjective original two-parameter evaluation is injective.
This uses the already native surjective nonzerodivisor dimension-drop theorem. -/
theorem completeLocalEval_injective_of_dimension_two
    (s : k →+* R) (x : Fin 2 → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (hspan : Ideal.span (Set.range x) = maximalIdeal R)
    (hres : Function.Surjective ((residue R).comp s)) (hdim : ringKrullDim R = 2) :
    Function.Injective (completeLocalEval s x hx) := by
  let : IsDomain (MvPowerSeries (Fin 2) k) := NoZeroDivisors.to_isDomain _
  apply (injective_iff_map_eq_zero (completeLocalEval s x hx)).mpr
  intro f hf
  by_contra hf0
  have hdrop := ringKrullDim_succ_le_of_surjective (completeLocalEval s x hx)
    (completeLocalEval_surjective s x hx hspan hres)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf0) hf
  have hbad : (3 : WithBot ℕ∞) ≤ 2 := by
    simpa only [hdim, show (2 : WithBot ℕ∞) + 1 = 3 from rfl] using
      hdrop.trans (ringKrullDim_twoVariable_le k)
  norm_num at hbad

/-- The forward map is literally native evaluation at the passed original coefficients
and two parameters. A finite parameter subring is never substituted for the target. -/
def completeLocalEquivTwo
    (s : k →+* R) (x : Fin 2 → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (hspan : Ideal.span (Set.range x) = maximalIdeal R)
    (hres : Function.Surjective ((residue R).comp s)) (hdim : ringKrullDim R = 2) :
    MvPowerSeries (Fin 2) k ≃+* R :=
  RingEquiv.ofBijective (completeLocalEval s x hx)
    ⟨completeLocalEval_injective_of_dimension_two s x hx hspan hres hdim,
      completeLocalEval_surjective s x hx hspan hres⟩

@[simp]
theorem completeLocalEquivTwo_C
    (s : k →+* R) (x : Fin 2 → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (hspan : Ideal.span (Set.range x) = maximalIdeal R)
    (hres : Function.Surjective ((residue R).comp s)) (hdim : ringKrullDim R = 2) (c : k) :
    completeLocalEquivTwo s x hx hspan hres hdim (C c) = s c :=
  completeLocalEval_C s x hx c

@[simp]
theorem completeLocalEquivTwo_X
    (s : k →+* R) (x : Fin 2 → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (hspan : Ideal.span (Set.range x) = maximalIdeal R)
    (hres : Function.Surjective ((residue R).comp s)) (hdim : ringKrullDim R = 2) (i : Fin 2) :
    completeLocalEquivTwo s x hx hspan hres hdim (X i) = x i :=
  completeLocalEval_X s x hx i

end TwoVariables

end MvPowerSeries
