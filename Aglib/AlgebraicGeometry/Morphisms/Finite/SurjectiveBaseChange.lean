/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finiteness reflected by an actual surjective target change

The full original cartesian point-lifting proof is uniquely lowered from
Curves.Normalization.FiniteFieldCover. No flatness or new fibre certificate
is required: properness and the finite original base change supply finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Actual point fibres descend along a surjective change of target. The only
point-lifting input is the universal geometric point existence theorem for the
original cartesian square, not a new cover or fibre certificate. -/
theorem finite_preimage_singleton_of_isPullback
    {P C Y X : Scheme.{u}} {a : P ⟶ C} {g : P ⟶ Y}
    {ν : C ⟶ X} {b : Y ⟶ X}
    (h : IsPullback a g ν b) [Surjective b] [IsFinite g] (x : X) :
    (ν ⁻¹' {x}).Finite := by
  obtain ⟨y, hy⟩ := b.surjective x
  apply ((g.finite_preimage_singleton y).image a).subset
  intro z hz
  change ν z = x at hz
  have hzy : ν.base z = b.base y := hz.trans hy.symm
  obtain ⟨w, haw, hgw⟩ := Scheme.exists_preimage_of_isPullback h z y hzy
  exact ⟨w, hgw, haw⟩

/-- A proper original morphism is finite if its base change along a surjective
map is finite. No flatness, field, Noetherian, or separate fibre hypothesis is used. -/
theorem isFinite_of_isProper_of_isPullback
    {P C Y X : Scheme.{u}} {a : P ⟶ C} {g : P ⟶ Y}
    {ν : C ⟶ X} {b : Y ⟶ X}
    (h : IsPullback a g ν b) [Surjective b] [IsFinite g] [IsProper ν] :
    IsFinite ν := by
  let : LocallyQuasiFinite ν :=
    LocallyQuasiFinite.of_finite_preimage_singleton ν
      (finite_preimage_singleton_of_isPullback h)
  exact IsFinite.of_isProper_of_locallyQuasiFinite ν

end AlgebraicGeometry.Scheme
