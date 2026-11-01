/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Normal stalks on an original open subscheme -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Normality restricts through the original open immersion's stalk isomorphism. -/
theorem NormalStalks.of_isOpenImmersion {X Y : Scheme.{u}} (hY : NormalStalks Y)
    (f : X ⟶ Y) [IsOpenImmersion f] : NormalStalks X := by
  intro x
  let : IsDomain (Y.presheaf.stalk (f x)) := (hY (f x)).1
  let : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := (hY (f x)).2
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end AlgebraicGeometry.Scheme
