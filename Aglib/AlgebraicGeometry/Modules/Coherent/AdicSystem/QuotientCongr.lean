/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient

/-! # Original quotient units under equality of ideal indices -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u v w

/-- Transport of a family of arrows only depends on its abstract target family. -/
theorem arrowFamily_eqToIso {C : Type u} [Category.{v} C] {T : Type w}
    (Q : T → C) {M : C} (η : ∀ t, M ⟶ Q t) {a b : T} (h : a = b) :
    η a ≫ (eqToIso (congrArg Q h)).hom = η b := by
  subst b
  simp

/-- Canonical transport bundled with its original-arrow equation. Native
consumers share this constructor rather than normalizing dependent casts. -/
def arrowFamilyIso {C : Type u} [Category.{v} C] {T : Type w}
    (Q : T → C) {M : C} (η : ∀ t, M ⟶ Q t) {a b : T} (h : a = b) :
    {e : Q a ≅ Q b // η a ≫ e.hom = η b} :=
  ⟨eqToIso (congrArg Q h), arrowFamily_eqToIso Q η h⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
