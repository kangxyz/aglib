/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Point injectivity over an open scheme chart

General declarations extracted from R5 baseline
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; names, chosen maps and hypotheses retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.OpenChartInjectivity` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ad8cb99fce802ead4fb4cdfd27f8fc724a23e030f2e2d7ef9ae343923274146a`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme pullback projection is injective on the inverse image of an open
source chart on which the original map is itself an open immersion. The proof
uses the iterated SCHEME pullback, not joint injectivity of its point projections. -/
theorem pullback_snd_eq_of_open_chart {V N C Z : Scheme.{u}}
    (j : V ⟶ N) (n : N ⟶ C) (f : Z ⟶ C) [IsOpenImmersion (j ≫ n)]
    (a b : ↑(pullback n f))
    (ha : pullback.fst n f a ∈ Set.range j)
    (hb : pullback.fst n f b ∈ Set.range j)
    (hab : pullback.snd n f a = pullback.snd n f b) : a = b := by
  let r := pullback.snd j (pullback.fst n f)
  have hs : IsPullback (pullback.fst j (pullback.fst n f))
      (r ≫ pullback.snd n f) (j ≫ n) f :=
    (IsPullback.of_hasPullback j (pullback.fst n f)).paste_vert
      (IsPullback.of_hasPullback n f)
  have : IsOpenImmersion (r ≫ pullback.snd n f) :=
    MorphismProperty.of_isPullback hs inferInstance
  obtain ⟨va, hva⟩ : ∃ v, r v = a := by
    change a ∈ Set.range (pullback.snd j (pullback.fst n f))
    rw [Scheme.Pullback.range_snd]
    exact ha
  obtain ⟨vb, hvb⟩ : ∃ v, r v = b := by
    change b ∈ Set.range (pullback.snd j (pullback.fst n f))
    rw [Scheme.Pullback.range_snd]
    exact hb
  have hv : va = vb := (r ≫ pullback.snd n f).isOpenEmbedding.injective (by
    simpa only [Scheme.Hom.comp_apply, hva, hvb] using hab)
  exact hva.symm.trans ((congrArg r hv).trans hvb)

end AlgebraicGeometry.Scheme.Hom
