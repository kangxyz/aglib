/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.PullbackFamilyRefinement

/-! # Full Cartesian coefficient sources factor through a target refinement

A map from an entire base-changed target stage to a chart induces a map from
an entire Cartesian coefficient pullback to the chart's family pullback. The
source is the literal pullback over the original coefficient base. A
commuting map to the finite source is used only as a map, not promoted to a
Cartesian square. The original projection laws are proved from the native
pullback lifts.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]
    {B B' X Y H : C} (g : B' ⟶ B) (b : Y ⟶ B) (a : Y ⟶ X) (t : H ⟶ X)
    [HasPullback g b] [HasPullback t a]
    [HasPullback g (pullback.snd t a ≫ b)]

/-- The canonical original-family projection from the full coefficient
pullback after the target refinement. -/
def pullback.coefficientRefinementOriginal :
    pullback g (pullback.snd t a ≫ b) ⟶ pullback g b :=
  pullback.lift (pullback.fst g (pullback.snd t a ≫ b))
    (pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.snd t a)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := g) (g := pullback.snd t a ≫ b)))

@[reassoc (attr := simp)]
theorem pullback.coefficientRefinementOriginal_fst :
    pullback.coefficientRefinementOriginal g b a t ≫ pullback.fst g b =
      pullback.fst g (pullback.snd t a ≫ b) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullback.coefficientRefinementOriginal_snd :
    pullback.coefficientRefinementOriginal g b a t ≫ pullback.snd g b =
      pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.snd t a :=
  pullback.lift_snd _ _ _

variable {X' : C} (f : X' ⟶ X) (p : pullback g b ⟶ X')
    (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasPullback t (p ≫ f)]

/-- The whole Cartesian coefficient source maps to the direct target-stage
base change of the original family over the finite source. -/
def pullback.coefficientRefinementFamily :
    pullback g (pullback.snd t a ≫ b) ⟶ pullback t (p ≫ f) :=
  pullback.lift
    (pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.fst t a)
    (pullback.coefficientRefinementOriginal g b a t) (by
      calc
        (pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.fst t a) ≫ t =
            pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.snd t a ≫ a := by
          rw [Category.assoc, pullback.condition]
        _ = pullback.coefficientRefinementOriginal g b a t ≫
            pullback.snd g b ≫ a := by
          rw [pullback.coefficientRefinementOriginal_snd_assoc]
        _ = pullback.coefficientRefinementOriginal g b a t ≫ (p ≫ f) := by
          rw [hp])

@[reassoc (attr := simp)]
theorem pullback.coefficientRefinementFamily_snd :
    pullback.coefficientRefinementFamily g b a t f p hp ≫ pullback.snd t (p ≫ f) =
      pullback.coefficientRefinementOriginal g b a t :=
  pullback.lift_snd _ _ _

variable {U : C} (u : U ⟶ X') [HasPullback t f] [HasPullback u p]
    (v : pullback t f ⟶ U) (hv : v ≫ u = pullback.snd t f)

/-- A genuine factorization of the entire target-stage pullback gives a
factorization of the entire coefficient pullback through the chart family. -/
def pullback.coefficientRefinementFactor :
    pullback g (pullback.snd t a ≫ b) ⟶ pullback u p :=
  pullback.coefficientRefinementFamily g b a t f p hp ≫
    pullback.familyRefinement t f p u v hv

/-- The full factorization retains its original coefficient-changed family map. -/
@[reassoc (attr := simp)]
theorem pullback.coefficientRefinementFactor_family :
    pullback.coefficientRefinementFactor g b a t f p hp u v hv ≫
      pullback.snd u p = pullback.coefficientRefinementOriginal g b a t := by
  simp only [pullback.coefficientRefinementFactor, Category.assoc,
    pullback.familyRefinement_snd, pullback.coefficientRefinementFamily_snd]

/-- The full factorization retains the exact original map to the family Y. -/
@[reassoc]
theorem pullback.coefficientRefinementFactor_original :
    pullback.coefficientRefinementFactor g b a t f p hp u v hv ≫
      pullback.snd u p ≫ pullback.snd g b =
        pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.snd t a := by
  simp only [pullback.coefficientRefinementFactor, Category.assoc,
    pullback.familyRefinement_snd_assoc,
    pullback.coefficientRefinementFamily_snd_assoc,
    pullback.coefficientRefinementOriginal_snd]

end CategoryTheory.Limits
