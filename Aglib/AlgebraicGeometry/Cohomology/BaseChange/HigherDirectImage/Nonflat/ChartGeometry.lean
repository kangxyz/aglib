/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Original cartesian geometry of affine chart pairs

The induced upper map is the original pullback lift. Its two projection laws
and cartesianness are proved from the same pasted square, independently of
coefficients, higher images or any base-change comparison.
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g)
  {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
  (hv : Spec.map σ ≫ j = v ≫ g)

/-- The original induced morphism between the actual source fibre products of a chart pair. -/
def chartUpper : Limits.pullback b v ⟶ Limits.pullback f j :=
  (IsPullback.of_hasPullback f j).lift
    (Limits.pullback.fst b v ≫ a) (Limits.pullback.snd b v ≫ Spec.map σ) (by
      have H := (IsPullback.of_hasPullback b v).paste_horiz h
      simpa only [Category.assoc, hv] using H.w)

/-- The chart map retains the original source projection. -/
@[reassoc]
theorem chartUpper_fst :
    chartUpper a b f g h j v σ hv ≫ Limits.pullback.fst f j =
      Limits.pullback.fst b v ≫ a :=
  (IsPullback.of_hasPullback f j).lift_fst _ _ _

/-- The chart map retains the original target projection and scalar morphism. -/
@[reassoc]
theorem chartUpper_snd :
    chartUpper a b f g h j v σ hv ≫ Limits.pullback.snd f j =
      Limits.pullback.snd b v ≫ Spec.map σ :=
  (IsPullback.of_hasPullback f j).lift_snd _ _ _

/-- Every chart pair of the original cartesian square is cartesian, with its actual induced
source map. -/
theorem chartUpper_isPullback :
    IsPullback (chartUpper a b f g h j v σ hv) (Limits.pullback.snd b v)
      (Limits.pullback.snd f j) (Spec.map σ) := by
  have H := (IsPullback.of_hasPullback b v).paste_horiz h
  have H' : IsPullback (Limits.pullback.fst b v ≫ a) (Limits.pullback.snd b v)
      f (Spec.map σ ≫ j) := by simpa only [hv] using H
  exact H'.of_right' (IsPullback.of_hasPullback f j)

end AlgebraicGeometry.Scheme.Modules.Nonflat
