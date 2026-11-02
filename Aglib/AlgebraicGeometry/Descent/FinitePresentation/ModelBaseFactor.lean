/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes

/-! # Actual finite-presentation models along a factorization of the base map -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent.Model

universe u

/-- Factor the actual base map and take the literal pullback model. The
original source and structural map remain the top left of the cartesian square. -/
def factorBase {S S₀ T Z : Scheme.{u}} {π : S ⟶ S₀} {t : Z ⟶ S}
    (M : Model π t) (a : S ⟶ T) (b : T ⟶ S₀) (h : a ≫ b = π) : Model a t := by
  let H : IsPullback M.p t M.f (a ≫ b) := by simpa only [h] using M.square
  let Q := IsPullback.of_hasPullback M.f b
  exact {
    X := Limits.pullback M.f b
    f := Limits.pullback.snd M.f b
    locallyOfFinitePresentation := inferInstance
    quasiCompact := inferInstance
    quasiSeparated := inferInstance
    p := Q.lift M.p (t ≫ a) (by simpa only [Category.assoc] using H.w)
    square := H.of_right' Q }


namespace Map

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Change the base of the original modeled arrow by the same native pullback
as `Model.factorBase`. Its original comparison square is retained. -/
def factorBase {S S₀ T Z W : Scheme.{u}} {π : S ⟶ S₀}
    {t : Z ⟶ S} {s : W ⟶ S} {M : Model π t} {N : Model π s}
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m)
    (b : S ⟶ T) (c : T ⟶ S₀) (h : b ≫ c = π) :
    Map (M.factorBase b c h) (N.factorBase b c h) m where
  hom := (Over.pullback c).map a.hom
  comm := by
    apply pullback.hom_ext (f := N.f) (g := c)
    · simp [Model.factorBase, Over.pullback_map_left, Category.assoc, a.comm]
    · have hm : m.left ≫ s = t := Over.w m
      simp [Model.factorBase, Over.pullback_map_left, Category.assoc, reassoc_of% hm]

end Map

end AlgebraicGeometry.Scheme.FinitePresentationDescent.Model
