/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.Analysis.LaurentSeries.EvaluationOperations
import Aglib.Analysis.LaurentSeries.PowerEvaluation
import Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.AlgebraicUnits
import Aglib.Analysis.Normed.Field.DVRNontrivial
import Aglib.Analysis.Normed.Field.UnramifiedDVR

/-! Focused consumers preserving the actual completion, coefficients, and partial domain. -/

noncomputable section

universe u v

example {F K : Type u} [Field F] [NormedField K] (f : F →+* K) :
    AlgebraicClosure.DenseEmbeddingExtends f ↔
      ∃ i : AlgebraicClosure F →+* K,
        i.comp (algebraMap F (AlgebraicClosure F)) = f ∧ DenseRange i := Iff.rfl

example (R F : Type u) [CommRing R] [NormedField F] [Algebra R F] :
    NormedField.NormCompatible R F ↔
      ∀ x : F, ‖x‖ ≤ 1 ↔ ∃ r : R, algebraMap R F r = x := Iff.rfl

open AlgebraicClosure.SpectralCompletion

example (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] [IsUltrametricDist F] (x : F) :
    embedding F x =
      algebraMap (AlgebraicClosure F) (Completed F) (algebraMap F (AlgebraicClosure F) x) := rfl

example (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] [IsUltrametricDist F] :
    Completed F = UniformSpace.Completion (AlgebraicClosure F) := rfl

open LaurentSeries.AllRadii

example {F : Type u} [NormedField F] (a : F) :
    Series.monomial (-1) a (-1) = a := by simp

example {F : Type u} [NormedField F] {K : Type v} [NormedField K] [CompleteSpace K]
    (f : F →+* K) [RingHomIsometric f] (u : Kˣ) (a : F) (n : ℤ) :
    Series.evaluate f u (Series.monomial n a) = f a * (u : K) ^ n :=
  Series.evaluate_monomial f u n a

example {F : Type u} [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    {K : Type v} [NormedField K] [CompleteSpace K]
    (f : F →+* K) [RingHomIsometric f] (u : Kˣ) (m : regularAt f u)
    (z : K) (hz : EvaluatesAt f u m z) : evaluationAt f u m = z :=
  evaluationAt_eq f u m z hz

example {F : Type u} [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    {K : Type v} [NormedField K] [CompleteSpace K]
    (f : F →+* K) [RingHomIsometric f] (u : Kˣ) (a : ℕ) (ha : 0 < a)
    {m : Meromorphic F} {z : K} (hm : EvaluatesAt f (u ^ a) m z) :
    EvaluatesAt f u (meromorphicPower a ha m) z :=
  hm.power f u a ha
