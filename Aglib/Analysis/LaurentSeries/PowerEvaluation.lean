/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.LaurentSeries.Evaluation

/-!
# Power substitution and partial evaluation

Source: `R5Lab.Aglib.Analysis.LaurentSeries.PowerEvaluation`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
namespace LaurentSeries.AllRadii
universe u v
variable {F : Type u} [NormedField F] [CompleteSpace F] [IsUltrametricDist F]
  {K : Type v} [NormedField K] [CompleteSpace K]
  (f : F →+* K) [RingHomIsometric f]

omit [IsUltrametricDist F] in
@[simp, nolint unusedArguments] theorem Series.evaluationHom_power [IsUltrametricDist F] (w :
  Kˣ) (a : ℕ) (ha : 0 < a) (c : Series F) :
    Series.evaluationHom f w (Series.power a ha c) = Series.evaluationHom f (w ^ a) c :=
  Series.evaluate_power f w a ha c

/-- Literal substitution preserves every qualifying fraction presentation.
The denominator is checked at w^a before evaluation; poles remain excluded. -/
theorem EvaluatesAt.power (w : Kˣ) (a : ℕ) (ha : 0 < a)
    {m : Meromorphic F} {z : K} (hm : EvaluatesAt f (w ^ a) m z) :
    EvaluatesAt f w (meromorphicPower a ha m) z := by
  obtain ⟨s, t, ht, rfl, rfl⟩ := hm
  refine ⟨Series.power a ha s, Series.power a ha t, ?_, ?_, ?_⟩
  · simpa only [Series.evaluationHom_power] using ht
  · simp only [map_div₀, meromorphicPower_algebraMap]
  · simp only [Series.evaluationHom_power]

end LaurentSeries.AllRadii
