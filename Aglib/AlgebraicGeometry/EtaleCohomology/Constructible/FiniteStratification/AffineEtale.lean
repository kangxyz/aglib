/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.NoetherianAffine
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Properties
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Finite strata for affine etale maps over arbitrary affine bases

The pinned native etale-model theorem descends the actual affine algebra to
an etale model over a finitely generated integer subalgebra. The proven
Noetherian partition of that model is pulled back through the original
cartesian model square. Canonical affine-scheme isomorphisms then retain
the original scheme morphism. No Noetherian base premise remains.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- The literal spectrum map of an actual etale algebra has a genuine
finite-etale partition over an arbitrary commutative base ring. -/
theorem exists_finitePartition_spec_of_etale (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    ∃ p : FiniteLocallyClosedPartition (Spec (CommRingCat.of A)),
      ∀ i, IsFinite (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) (p.inclusion i)) := by
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ A B
  have : Algebra.Etale A₀ B₀ := hB₀
  have : IsNoetherianRing A₀ := isNoetherianRing_of_fg hA₀
  let f₀ : Spec (CommRingCat.of B₀) ⟶ Spec (CommRingCat.of A₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  have : Etale f₀ :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hB₀)
  obtain ⟨p, hp⟩ := exists_finitePartition_of_isAffineHom_of_noetherian f₀
  let g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B₀) :=
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] A ⊗[A₀] B₀).toRingHom))
  have H : IsPullback a f f₀ g := Scheme.isPullback_affineModelMap A₀ A B₀ B e.symm
  exact ⟨p.baseChange g,
    FiniteLocallyClosedPartition.finite_baseChange f₀ f a g H p hp⟩

/-- An actual affine etale morphism over an affine base admits a finite
constructible locally closed partition with all original base-changed
structural maps finite. There is no Noetherian hypothesis. -/
theorem exists_finitePartition_of_isAffineHom_of_etale
    {Y X : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f] :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i, IsFinite (pullback.snd f (p.inclusion i)) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let A := Γ(X, ⊤)
  let B := Γ(Y, ⊤)
  let φ : A →+* B := f.appTop.hom
  let : Algebra A B := φ.toAlgebra
  have : Algebra.Etale A B :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  obtain ⟨p, hp⟩ := exists_finitePartition_spec_of_etale A B
  let g : X ⟶ Spec (CommRingCat.of A) := X.isoSpec.hom
  let a : Y ⟶ Spec (CommRingCat.of B) := Y.isoSpec.hom
  let f₀ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have H : IsPullback a f f₀ g :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
  exact ⟨p.baseChange g,
    FiniteLocallyClosedPartition.finite_baseChange f₀ f a g H p hp⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
