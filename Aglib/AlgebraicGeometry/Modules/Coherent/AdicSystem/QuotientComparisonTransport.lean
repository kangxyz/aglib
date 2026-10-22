/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCongr

/-! # Whole unit-compatible comparisons under index transport -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u v w

/-- Compose an original unit-compatible isomorphism with canonical transport.
All constructors and arrows stay abstract until the whole result is formed. -/
def arrowFamilyComparison {C : Type u} [Category.{v} C] {T : Type w}
    (Q : T → C) {M N : C} (η : ∀ t, M ⟶ Q t) {a b : T}
    (u : M ⟶ N) (e : N ≅ Q a) (he : u ≫ e.hom = η a) (h : a = b) :
    {d : N ≅ Q b // u ≫ d.hom = η b} := by
  let c := arrowFamilyIso Q η h
  refine ⟨e ≪≫ c.val, ?_⟩
  change u ≫ e.hom ≫ c.val.hom = η b
  rw [← Category.assoc, he]
  exact c.property

end AlgebraicGeometry.Scheme.Modules.Coherent
