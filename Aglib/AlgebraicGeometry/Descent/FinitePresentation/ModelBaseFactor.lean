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

end AlgebraicGeometry.Scheme.FinitePresentationDescent.Model
