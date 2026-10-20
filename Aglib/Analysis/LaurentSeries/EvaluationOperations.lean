/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.LaurentSeries.Evaluation
public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.Algebra.Polynomial.Inductions

/-!
# Operations on qualifying fraction evaluations

Source: `R5Lab.Aglib.Analysis.LaurentSeries.EvaluationOperations`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LaurentSeries.AllRadii
universe u
variable {F K : Type u} [NormedField F] [CompleteSpace F] [CharZero F]
  [IsUltrametricDist F] [NormedField K] [CompleteSpace K] [CharZero K]
  [IsUltrametricDist K]
variable (f : F →+* K) [RingHomIsometric f] (w : Kˣ)

omit [CharZero F] [IsUltrametricDist F] [CharZero K] [IsUltrametricDist K] in
@[nolint unusedArguments] theorem Series.evaluationHom_constant [CharZero F]
  [IsUltrametricDist F] [CharZero K] [IsUltrametricDist K] (a : F) :
    Series.evaluationHom f w (algebraMap F (Series F) a) = f a := by
  change Series.evaluate f w _ = _
  rw [Series.algebraMap_eq_monomial, Series.evaluate_monomial]
  simp

theorem evaluatesAt_constant (a : F) :
    EvaluatesAt f w (algebraMap F (Meromorphic F) a) (f a) := by
  convert evaluatesAt_algebraMap f w (algebraMap F (Series F) a) using 1
  exact (Series.evaluationHom_constant f w a).symm

omit [CharZero F] [CharZero K] [IsUltrametricDist K] in
@[nolint unusedArguments]
theorem EvaluatesAt.sub [CharZero F] [CharZero K] [IsUltrametricDist K] {m n : Meromorphic F} {z
  t : K}
    (hm : EvaluatesAt f w m z) (hn : EvaluatesAt f w n t) :
    EvaluatesAt f w (m - n) (z - t) := by
  simpa only [sub_eq_add_neg] using hm.add f w (hn.neg f w)

theorem evaluatesAt_zero : EvaluatesAt f w (0 : Meromorphic F) 0 := by
  simpa using evaluatesAt_constant f w 0

theorem evaluatesAt_one : EvaluatesAt f w (1 : Meromorphic F) 1 := by
  simpa using evaluatesAt_constant f w 1

theorem EvaluatesAt.pow {m : Meromorphic F} {z : K}
    (hm : EvaluatesAt f w m z) (n : ℕ) : EvaluatesAt f w (m ^ n) (z ^ n) := by
  induction n with
  | zero => simpa using evaluatesAt_one f w
  | succ n ih => simpa only [pow_succ] using ih.mul f w hm

theorem EvaluatesAt.polynomial {m : Meromorphic F} {z : K}
    (hm : EvaluatesAt f w m z) (p : Polynomial F) :
    EvaluatesAt f w (Polynomial.eval₂ (algebraMap F (Meromorphic F)) m p)
      (Polynomial.eval₂ f z p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simpa only [Polynomial.eval₂_add] using hp.add f w hr
  | monomial n a =>
    simpa only [Polynomial.eval₂_monomial] using
      (evaluatesAt_constant f w a).mul f w (hm.pow f w n)

theorem EvaluatesAt.bivariate {m n : Meromorphic F} {z t : K}
    (hm : EvaluatesAt f w m z) (hn : EvaluatesAt f w n t)
    (p : Polynomial (Polynomial F)) :
    EvaluatesAt f w
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap F (Meromorphic F)) m) n p)
      (Polynomial.eval₂ (Polynomial.eval₂RingHom f z) t p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simpa only [Polynomial.eval₂_add] using hp.add f w hr
  | monomial j a =>
    simpa only [Polynomial.eval₂_monomial, Polynomial.coe_eval₂RingHom] using
      (hm.polynomial f w a).mul f w (hn.pow f w j)

omit [CharZero F] [CharZero K] [IsUltrametricDist K] in
@[nolint unusedArguments]
theorem EvaluatesAt.inv [CharZero F] [CharZero K] [IsUltrametricDist K] {m : Meromorphic F} {z : K}
    (hm : EvaluatesAt f w m z) (hz : z ≠ 0) : EvaluatesAt f w m⁻¹ z⁻¹ := by
  obtain ⟨a, b, hb, rfl, rfl⟩ := hm
  refine ⟨b, a, (div_ne_zero_iff.mp hz).1, ?_, ?_⟩ <;> rw [inv_div]

/-- Division is allowed only when the actual denominator value is nonzero. -/
theorem EvaluatesAt.div {m n : Meromorphic F} {z t : K}
    (hm : EvaluatesAt f w m z) (hn : EvaluatesAt f w n t) (ht : t ≠ 0) :
    EvaluatesAt f w (m / n) (z / t) := by
  simpa only [div_eq_mul_inv] using hm.mul f w (hn.inv f w ht)

end LaurentSeries.AllRadii
