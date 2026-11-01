/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.SectionNoetherianDescent
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusRestriction
public import Aglib.AlgebraicGeometry.Spec.HartogsFiniteAlgebraEtaleDetection
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles

/-! # The original standard-smooth section locus over an arbitrary affine base

Section-preserving Noetherian descent supplies a genuine original affine
cartesian square. The whole section equation gives its original compatible
sections. Literal preimage of the accepted Noetherian locus proves openness;
quasi-compactness of the actual affine map proves retrocompactness. No
Noetherian, field, or perfectness hypothesis is imposed on the original base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme
universe u

private theorem spec_section_structural
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (σ : B →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.algebraMap R B = 𝟙 _ := by
  simpa [Spec.algebraMap] using Spec.map_algHom_algebraMap σ

/-- The actual section-component locus of an original standard smooth affine
family is open and retrocompact over an arbitrary commutative base ring. -/
theorem standardSectionComponentLocus_isOpen_isRetrocompact
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R B]
    (σ : B →ₐ[R] R)
    (hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.algebraMap R B = 𝟙 _) :
    IsOpen (sectionComponentLocus (Spec.algebraMap R B)
      (Spec.map (CommRingCat.ofHom σ.toRingHom)) hσ) ∧
    IsRetrocompact (sectionComponentLocus (Spec.algebraMap R B)
      (Spec.map (CommRingCat.ofHom σ.toRingHom)) hσ) := by
  obtain ⟨S, D, hD, hSD, hS, hstandard, e, τ, he⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg_with_section R B n σ
  let : CommRing D := hD
  let : Algebra S D := hSD
  let : Algebra.IsStandardSmoothOfRelativeDimension n S D := hstandard
  let : Algebra.FiniteType ℤ S := S.fg_iff_finiteType.mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let f : Spec (.of D) ⟶ Spec (.of S) := Spec.algebraMap S D
  let p : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let b : Spec (.of R) ⟶ Spec (.of S) := Spec.algebraMap S R
  let m : D →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : D →ₐ[S] R ⊗[S] D).toRingHom
  let a : Spec (.of B) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom m)
  let σ₀ : Spec (.of S) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom τ.toRingHom)
  let σR : Spec (.of R) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hσ₀ : σ₀ ≫ f = 𝟙 _ := spec_section_structural τ
  have H : IsPullback a p f b := (isPullback_of_tensorAlgEquiv S R D B e).flip
  have hm : σ.toRingHom.comp m = (algebraMap S R).comp τ.toRingHom := by
    ext d
    change σ (e (1 ⊗ₜ[S] d)) = algebraMap S R (τ d)
    have h := AlgHom.congr_fun he (1 ⊗ₜ[S] d)
    simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul, Algebra.ofId_apply] using h
  have hsections : σR ≫ a = b ≫ σ₀ := by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom m) =
      Spec.map (CommRingCat.ofHom (algebraMap S R)) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hm]
  let : SmoothOfRelativeDimension n f := by
    change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap S D)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hstandard
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hpre := sectionComponentLocus_preimage_of_isPullback f a p b H
    σ₀ hσ₀ σR hσ hsections
  obtain ⟨hopen, hretro⟩ := sectionComponentLocus_isOpen_isRetrocompact S f n σ₀ hσ₀
  have hopenR : IsOpen (sectionComponentLocus p σR hσ) := by
    rw [← hpre]
    exact hopen.preimage a.continuous
  have hcompact : IsCompact (sectionComponentLocus p σR hσ) := by
    rw [← hpre]
    exact QuasiCompact.isCompact_preimage (f := a) _ hopen hretro.isCompact
  exact ⟨hopenR, hcompact.isRetrocompact hopenR⟩

end AlgebraicGeometry.Scheme
