/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Concrete relative quasi-affine factorization from an affine source

A map from an affine scheme factors as its graph into the product over the
terminal scheme, followed by the second projection. The graph is an immersion
and that projection is affine. No finite-type or Noetherian hypothesis and
no affineness assumption on the target is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Every map from an affine scheme has an actual immersion-affine
factorization, retaining the original composite over an arbitrary target. -/
theorem exists_immersion_affine_factorization_of_isAffine
    {Y X : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X) :
    ∃ (P : Scheme.{u}) (e : Y ⟶ P) (a : P ⟶ X),
      IsImmersion e ∧ IsAffineHom a ∧ e ≫ a = f := by
  let P : Scheme.{u} := pullback (terminal.from Y) (terminal.from X)
  let e : Y ⟶ P := pullback.lift (𝟙 Y) f (by simp)
  let a : P ⟶ X := pullback.snd (terminal.from Y) (terminal.from X)
  have hfst : e ≫ pullback.fst (terminal.from Y) (terminal.from X) = 𝟙 Y :=
    pullback.lift_fst _ _ _
  let : IsImmersion (e ≫ pullback.fst (terminal.from Y) (terminal.from X)) := by
    rw [hfst]
    infer_instance
  have ha : IsAffineHom a :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      X Y P (⊤_ Scheme.{u}) (terminal.from X) (terminal.from Y)
      (pullback.fst (terminal.from Y) (terminal.from X))
      (pullback.snd (terminal.from Y) (terminal.from X))
      (IsPullback.of_hasPullback (terminal.from Y) (terminal.from X))
      (inferInstance : IsAffineHom (terminal.from Y))
  refine ⟨P, e, a, IsImmersion.of_comp e (pullback.fst _ _), ha, ?_⟩
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme
