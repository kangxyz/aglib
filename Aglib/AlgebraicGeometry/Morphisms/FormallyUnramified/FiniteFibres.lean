/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Unramified.FiniteFibres
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Finite morphisms with formally unramified fibres

This criterion uses the original scheme-theoretic residue fibres. It does
not assert flatness or etaleness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A finite morphism with formally unramified residue fibres is formally
unramified, without a Noetherian or flatness assumption. -/
theorem FormallyUnramified.of_isFinite_of_fiberToSpecResidueField
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f]
    (hf : ∀ y, FormallyUnramified (f.fiberToSpecResidueField y)) :
    FormallyUnramified f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    apply this (pullback.snd f (Y.affineCover.f i)) _ ⟨_, rfl⟩
    intro y
    exact MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback f (Y.affineCover.f i)) y) (hf _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · let instAffine : IsAffine X := isAffine_of_isAffineHom f
    have h : FormallyUnramified (X.isoSpec.inv ≫ f) := by
      apply this (X.isoSpec.inv ≫ f) _ ⟨_, rfl⟩
      intro y
      let a := pullback.map (X.isoSpec.inv ≫ f) ((Spec R).fromSpecResidueField y)
        f ((Spec R).fromSpecResidueField y) X.isoSpec.inv (𝟙 _) (𝟙 _) (by simp) (by simp)
      have h : FormallyUnramified (a ≫ f.fiberToSpecResidueField y) :=
        MorphismProperty.comp_mem @FormallyUnramified _ _
          (MorphismProperty.of_isIso _ a) (hf y)
      simpa only [a, Scheme.Hom.fiberToSpecResidueField,
        pullback.map, pullback.lift_snd, Category.comp_id] using h
    exact (MorphismProperty.cancel_left_of_respectsIso @FormallyUnramified _ _).mp h
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have : Module.Finite R B := (IsFinite.SpecMap_iff φ).mp inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  change Algebra.FormallyUnramified R B
  apply Algebra.formallyUnramified_of_finite_of_residueField_tensorProduct
  intro p
  have h := (MorphismProperty.arrow_mk_iso_iff (P := @FormallyUnramified)
    (Spec.fiberToSpecResidueFieldIso R B p)).mp (hf p)
  exact RingHom.formallyUnramified_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp h)

end AlgebraicGeometry
