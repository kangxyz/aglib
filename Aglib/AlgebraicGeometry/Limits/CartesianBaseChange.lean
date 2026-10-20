/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Canonical base change of a cartesian square

Original source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
The mathematical declarations, explicit conditions and source boundaries are unchanged.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.CartesianBaseChange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`28539a06c7b2e6cc73f241db17e4d6e46415e1eca80a6372e2f3fd47bfc94d9e`.
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

namespace AlgebraicGeometry.Scheme.Pullback.CartesianBaseChange
variable {C Y A B A' B' : Scheme.{u}}
    (j : C ⟶ Y) (e : C ⟶ A) (π : Y ⟶ B) (t : A ⟶ B)
    (h : IsPullback j e π t)
    (f : A' ⟶ A) (b : B' ⟶ B) (t' : A' ⟶ B') (w : t' ≫ b = f ≫ t)

/-- The generic map is an explicit lift into the literal base-changed model. -/
def genericBaseChange : pullback e f ⟶ pullback π b :=
  pullback.lift (pullback.fst e f ≫ j) (pullback.snd e f ≫ t') (by
    simp only [Category.assoc, h.w, w]
    rw [← Category.assoc, pullback.condition]
    simp only [Category.assoc])

/-- Base-changing the model and generic field along a commuting square
preserves the actual generic pullback square; no new square is supplied. -/
theorem genericBaseChange_isPullback :
    IsPullback (genericBaseChange j e π t h f b t' w) (pullback.snd e f)
      (pullback.snd π b) t' := by
  refine ⟨⟨by simp [genericBaseChange]⟩,
    ⟨PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  have hc : (s.fst ≫ pullback.fst π b) ≫ π = (s.snd ≫ f) ≫ t := by
    calc
      (s.fst ≫ pullback.fst π b) ≫ π = s.fst ≫ pullback.snd π b ≫ b := by
        simp [Category.assoc, pullback.condition]
      _ = s.snd ≫ t' ≫ b := by rw [← Category.assoc, s.condition]; simp [Category.assoc]
      _ = (s.snd ≫ f) ≫ t := by rw [w]; simp [Category.assoc]
  let x := h.lift (s.fst ≫ pullback.fst π b) (s.snd ≫ f) hc
  let a := pullback.lift x s.snd (h.lift_snd _ _ hc)
  refine ⟨a, ?_, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp [a, x, genericBaseChange, Category.assoc]
    · simpa [a, genericBaseChange, Category.assoc] using s.condition.symm
  · simp [a]
  · intro q hq₁ hq₂
    change q ≫ genericBaseChange j e π t h f b t' w = s.fst at hq₁
    change q ≫ pullback.snd e f = s.snd at hq₂
    apply pullback.hom_ext (f := e) (g := f)
    · simp only [a, pullback.lift_fst]
      apply h.hom_ext
      · calc
          (q ≫ pullback.fst e f) ≫ j =
              (q ≫ genericBaseChange j e π t h f b t' w) ≫ pullback.fst π b := by
            simp [genericBaseChange, Category.assoc]
          _ = s.fst ≫ pullback.fst π b := by rw [hq₁]
          _ = x ≫ j := (h.lift_fst _ _ hc).symm
      · calc
          (q ≫ pullback.fst e f) ≫ e = (q ≫ pullback.snd e f) ≫ f := by
            simp [Category.assoc, pullback.condition]
          _ = s.snd ≫ f := by rw [hq₂]
          _ = x ≫ e := (h.lift_snd _ _ hc).symm
    · simpa [a] using hq₂
end AlgebraicGeometry.Scheme.Pullback.CartesianBaseChange
