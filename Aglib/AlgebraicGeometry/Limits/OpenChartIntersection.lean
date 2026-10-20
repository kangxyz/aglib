/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Cartesian intersections through open charts

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, universes, maps and mathematical hypotheses are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.OpenChartIntersection` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`836c8adec02ced6f400fd9d73ee74f786f6a4b34b2d6bd5d89f009505f6a065e`.
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

section OpenChartIntersectionExtension

/-!
Extend an already constructed scheme-theoretic intersection through exact
open-chart pullbacks when its full ambient support remains in that common
open chart. This is a universal-property statement for schemes; it assumes
no chain, component inventory, count, or global intersection conclusion.
-/
noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Exact old intersection squares extend through two open source charts when
the actual intersection of the ambient images is supported in the common
open target chart. The conclusion retains the two composed endpoint maps. -/
lemma isPullback_of_openCharts_of_range_inter
    {P A B U A' B' Y : Scheme.{u}}
    (j : U ⟶ Y) (a : A ⟶ A') (b : B ⟶ B')
    [IsOpenImmersion j] [IsOpenImmersion a] [IsOpenImmersion b]
    (c : A ⟶ U) (d : B ⟶ U) (f : A' ⟶ Y) (g : B' ⟶ Y)
    (s : P ⟶ A) (t : P ⟶ B)
    (Hf : IsPullback c a j f) (Hg : IsPullback d b j g)
    (Hold : IsPullback s t c d)
    (hsupp : Set.range f ∩ Set.range g ⊆ Set.range j) :
    IsPullback (s ≫ a) (t ≫ b) f g := by
  have w : (s ≫ a) ≫ f = (t ≫ b) ≫ g := by
    calc
      (s ≫ a) ≫ f = (s ≫ c) ≫ j := by rw [Category.assoc, ← Hf.w, ← Category.assoc]
      _ = (t ≫ d) ≫ j := by rw [Hold.w]
      _ = (t ≫ b) ≫ g := by rw [Category.assoc, Hg.w, ← Category.assoc]
  let common : ∀ q : PullbackCone f g, q.pt ⟶ U := fun q =>
    IsOpenImmersion.lift j (q.fst ≫ f) (by
      rintro _ ⟨x, rfl⟩
      apply hsupp
      constructor
      · exact ⟨q.fst x, rfl⟩
      · refine ⟨q.snd x, ?_⟩
        change (q.snd ≫ g) x = (q.fst ≫ f) x
        rw [q.condition])
  have common_fac (q : PullbackCone f g) : common q ≫ j = q.fst ≫ f :=
    IsOpenImmersion.lift_fac j (q.fst ≫ f) _
  let liftA : ∀ q : PullbackCone f g, q.pt ⟶ A := fun q =>
    Hf.lift (common q) q.fst (common_fac q)
  let liftB : ∀ q : PullbackCone f g, q.pt ⟶ B := fun q =>
    Hg.lift (common q) q.snd ((common_fac q).trans q.condition)
  have common_eq (q : PullbackCone f g) : liftA q ≫ c = liftB q ≫ d := by
    dsimp only [liftA, liftB]
    rw [Hf.lift_fst, Hg.lift_fst]
  let lifted : ∀ q : PullbackCone f g, q.pt ⟶ P := fun q =>
    Hold.lift (liftA q) (liftB q) (common_eq q)
  have lifted_left (q : PullbackCone f g) : lifted q ≫ (s ≫ a) = q.fst := by
    dsimp only [lifted]
    rw [Hold.lift_fst_assoc]
    exact Hf.lift_snd (common q) q.fst (common_fac q)
  have lifted_right (q : PullbackCone f g) : lifted q ≫ (t ≫ b) = q.snd := by
    dsimp only [lifted]
    rw [Hold.lift_snd_assoc]
    exact Hg.lift_snd (common q) q.snd ((common_fac q).trans q.condition)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w lifted lifted_left lifted_right (by
    intro q e heA heB
    apply Hold.hom_ext
    · apply (cancel_mono a).mp
      simpa only [Category.assoc] using heA.trans (lifted_left q).symm
    · apply (cancel_mono b).mp
      simpa only [Category.assoc] using heB.trans (lifted_right q).symm))

end AlgebraicGeometry

end -- noncomputable section
end OpenChartIntersectionExtension
