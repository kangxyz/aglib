/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.GenericFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties

/-! # A finite open part of an actual affine quasi-finite morphism

Generic algebraic finiteness is transported through the canonical affine
scheme isomorphisms and the native tensor-product pullback. The output is an
actual nonempty open immersion into the original integral affine base, with
the original structural morphism finite after that literal base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- Iterating base change retains finiteness of the actual structural map. -/
theorem isFinite_pullback_snd_comp_iff {Y X S T : Scheme.{u}}
    (f : Y ⟶ X) (g : S ⟶ X) (h : T ⟶ S) :
    IsFinite (pullback.snd f (h ≫ g)) ↔
      IsFinite (pullback.snd (pullback.snd f g) h) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite
    (pullbackLeftPullbackSndIso f g h).hom,
    pullbackLeftPullbackSndIso_hom_snd]

/-- An actual affine quasi-finite morphism of finite type over an integral
affine base is finite on an actual nonempty open part of that base. -/
theorem exists_nonempty_finite_open_of_isAffineHom
    {Y X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (f : Y ⟶ X) [IsAffineHom f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    ∃ (S : Scheme.{u}) (j : S ⟶ X),
      IsOpenImmersion j ∧ Nonempty S ∧ IsFinite (pullback.snd f j) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let A := Γ(X, ⊤)
  let B := Γ(Y, ⊤)
  let φ : A →+* B := f.appTop.hom
  let : Algebra A B := φ.toAlgebra
  have : Algebra.QuasiFinite A B :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mp inferInstance
  have : Algebra.FiniteType A B :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  obtain ⟨a, ha, hfinite⟩ := Algebra.QuasiFinite.exists_nonzero_finite_baseChange_away A B
  let R := Localization.Away a
  have : IsDomain R := Localization.Away.isDomain ha
  let S := Spec (CommRingCat.of R)
  let p : S ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A R))
  let f' : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let j : S ⟶ X := p ≫ X.isoSpec.inv
  have hfiniteSpec : IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[A] B)))) := by
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have hfiniteProjection : IsFinite (pullback.fst p f') := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (pullbackSpecIso A R B).inv, pullbackSpecIso_inv_fst']
    exact hfiniteSpec
  have H : IsPullback (pullback.snd p f' ≫ Y.isoSpec.inv)
      (pullback.fst p f') f j := by
    refine (IsPullback.of_hasPullback p f').flip.of_iso'
      (.refl _) Y.isoSpec (.refl _) X.isoSpec ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact Scheme.isoSpec_hom_naturality f
    · simp [j]
  refine ⟨S, j, inferInstance, inferInstance, ?_⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite H.isoPullback.hom,
    H.isoPullback_hom_snd]
  exact hfiniteProjection

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
