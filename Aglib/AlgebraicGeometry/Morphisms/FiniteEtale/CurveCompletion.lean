/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.EtaleCurve
public import Aglib.AlgebraicGeometry.Normalization.OpenFiniteRestriction
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Actual finite completion of finite-etale covers of open field curves

The original map is factored through its native relative normalization.
The finite map on the original open is recovered by an actual Cartesian
square. The ambient curve need not be normal, and neither the cover nor
the open is required to be connected or nonempty. The base field is unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An actual finite-etale cover of an open in an integral field curve
extends to a finite morphism, with dense open original source and the exact
original finite cover as its Cartesian restriction. -/
theorem exists_finite_completion_of_fieldCurve
    {k : Type u} [Field k] {V U X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1)
    (v : V ⟶ U) [IsFinite v] [Etale v]
    (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (Y : Scheme.{u}) (j' : V ⟶ Y) (b : Y ⟶ X),
      IsOpenImmersion j' ∧ IsDominant j' ∧ IsFinite b ∧ IsPullback j' v b j := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let f := v ≫ j
  let : IsFinite f.fromNormalization :=
    Hom.isFinite_fromNormalization_of_etale_fieldCurve p hdim f
  exact ⟨f.normalization, f.toNormalization, f.fromNormalization,
    inferInstance, inferInstance, inferInstance,
    Hom.isPullback_toNormalization_of_finite_open v j⟩

/-- Properness of the completed curve is over the same supplied field,
through the displayed finite map and the original proper structure morphism. -/
theorem exists_finite_proper_completion_of_fieldCurve
    {k : Type u} [Field k] {V U X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    (v : V ⟶ U) [IsFinite v] [Etale v]
    (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ (Y : Scheme.{u}) (j' : V ⟶ Y) (b : Y ⟶ X),
      IsOpenImmersion j' ∧ IsDominant j' ∧ IsFinite b ∧
        IsProper (b ≫ p) ∧ IsPullback j' v b j := by
  obtain ⟨Y, j', b, hj', hdense, hb, H⟩ :=
    exists_finite_completion_of_fieldCurve p hdim v j
  let := hb
  exact ⟨Y, j', b, hj', hdense, hb, inferInstance, H⟩

end AlgebraicGeometry.Scheme
