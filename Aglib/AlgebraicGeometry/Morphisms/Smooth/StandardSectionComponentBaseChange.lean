/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.StandardSectionComponentRestriction
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RationalPointEtaleLocal

/-! # The original tensor-base-change section-component restriction

The actual affine tensor square and the original supplied algebra map define
the native pullback section. Its component locus is open and retrocompact,
and its actual open restriction retains the same section, projections and
point membership. No etale neighborhood or prescribed-point coverage is
assumed: those are separate inputs to the final local factorization.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme
universe u

/-- Openness and retrocompactness for the original native pullback and its
original algebra-map section, not a replacement tensor-product scheme. -/
theorem standardBaseChangeSection_locus_isOpen_isRetrocompact
    (R B T : Type u) [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra R T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R B] (ε : B →ₐ[R] T) :
    IsOpen (sectionComponentLocus
      (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T))
      (rationalPointBaseChangeSection ε) (rationalPointBaseChangeSection_snd ε)) ∧
    IsRetrocompact (sectionComponentLocus
      (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T))
      (rationalPointBaseChangeSection ε) (rationalPointBaseChangeSection_snd ε)) := by
  let D := T ⊗[R] B
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let b : Spec (.of T) ⟶ Spec (.of R) := Spec.algebraMap R T
  let Y : Scheme.{u} := pullback f b
  let q : Y ⟶ Spec (.of T) := pullback.snd f b
  let qD : Spec (.of D) ⟶ Spec (.of T) := Spec.algebraMap T D
  let a : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[R] D).toRingHom)
  have H : IsPullback a qD f b :=
    (isPullback_of_tensorAlgEquiv R T B D (AlgEquiv.refl)).flip
  let e : Spec (.of D) ≅ Y := H.isoPullback
  let εD : D →ₐ[T] T := Algebra.TensorProduct.lift (AlgHom.id T T) ε
    (fun _ _ => Commute.all _ _)
  let σD : Spec (.of T) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom εD.toRingHom)
  let σY : Spec (.of T) ⟶ Y := rationalPointBaseChangeSection ε
  have hσD : σD ≫ qD = 𝟙 _ := by
    simpa [σD, qD, Spec.algebraMap] using Spec.map_algHom_algebraMap εD
  have hε : εD.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] D).toRingHom = ε.toRingHom := by
    ext x
    exact (Algebra.TensorProduct.lift_tmul (AlgHom.id T T) ε
      (fun _ _ => Commute.all _ _) 1 x).trans (one_mul _)
  have hσDe : σD ≫ e.hom = σY := by
    apply pullback.hom_ext
    · rw [Category.assoc, H.isoPullback_hom_fst, rationalPointBaseChangeSection_fst]
      change Spec.map (CommRingCat.ofHom εD.toRingHom) ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] D).toRingHom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]
    · rw [Category.assoc, H.isoPullback_hom_snd, rationalPointBaseChangeSection_snd]
      exact hσD
  have hq : e.inv ≫ qD = q := H.isoPullback_inv_snd
  have He : IsPullback e.inv q qD (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨hq.trans (Category.comp_id q).symm⟩
  have hsections : σY ≫ e.inv = (𝟙 _) ≫ σD := by
    rw [← hσDe, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  let : SmoothOfRelativeDimension n qD := by
    change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap T D)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  let : Smooth qD := SmoothOfRelativeDimension.smooth n qD
  have hpre := sectionComponentLocus_preimage_of_isPullback qD e.inv q (𝟙 _) He
    σD hσD σY (rationalPointBaseChangeSection_snd ε) hsections
  obtain ⟨U, τ, hU, _, _, _, hqc, _, _, _, _⟩ :=
    exists_standardSectionComponent_restriction T D n εD hσD
  let : QuasiCompact (U.ι ≫ qD) := hqc
  let : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ qD)
  have hcU : IsCompact (U : Set (Spec (.of D))) := by
    have h := isCompact_univ.image U.ι.continuous
    simpa only [Set.image_univ, Opens.range_ι] using h
  have ho : IsOpen (sectionComponentLocus q σY (rationalPointBaseChangeSection_snd ε)) := by
    rw [← hpre, ← hU]
    exact U.isOpen.preimage e.inv.continuous
  have hr : IsRetrocompact
      (sectionComponentLocus q σY (rationalPointBaseChangeSection_snd ε)) := by
    rw [← hpre, ← hU]
    exact IsRetrocompact.preimage_of_isOpenEmbedding e.inv.isOpenEmbedding
      (hcU.isRetrocompact U.isOpen)
  exact ⟨ho, hr⟩

/-- The actual native base-change section-component open has the original
section triangles, smooth geometrically connected qcqs structure, and the
literal point-membership interface needed by prescribed-point descent. -/
theorem exists_standardBaseChangeSection_restriction
    (R B T : Type u) [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra R T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R B] (ε : B →ₐ[R] T) :
    ∃ (W : (pullback (Spec.algebraMap R B) (Spec.algebraMap R T) : Scheme.{u}).Opens)
      (τ : Spec (.of T) ⟶ W.toScheme),
      (W : Set (pullback (Spec.algebraMap R B) (Spec.algebraMap R T) : Scheme.{u})) =
        sectionComponentLocus (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T))
          (rationalPointBaseChangeSection ε) (rationalPointBaseChangeSection_snd ε) ∧
      τ ≫ W.ι = rationalPointBaseChangeSection ε ∧
      τ ≫ (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) = 𝟙 _ ∧
      SmoothOfRelativeDimension n
        (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ∧
      QuasiCompact (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ∧
      QuasiSeparated (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ∧
      GeometricallyConnected (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ∧
      UniversallyOpen (W.ι ≫ pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) := by
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let b : Spec (.of T) ⟶ Spec (.of R) := Spec.algebraMap R T
  let Y : Scheme.{u} := pullback f b
  let q : Y ⟶ Spec (.of T) := pullback.snd f b
  let σ := rationalPointBaseChangeSection ε
  let hσ := rationalPointBaseChangeSection_snd ε
  let : SmoothOfRelativeDimension n f := by
    change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  let : SmoothOfRelativeDimension n q :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension n)
      (smoothOfRelativeDimension_isStableUnderBaseChange n)
      (Spec (.of T)) (Spec (.of B)) Y (Spec (.of R)) b f (pullback.fst f b) q
      (IsPullback.of_hasPullback f b) (inferInstance : SmoothOfRelativeDimension n f)
  let : Smooth q := SmoothOfRelativeDimension.smooth n q
  obtain ⟨hopen, hretro⟩ := standardBaseChangeSection_locus_isOpen_isRetrocompact R B T n ε
  let W := sectionComponentOpen q σ hσ hopen
  obtain ⟨τ, hτ, hτq⟩ := exists_sectionComponentOpen_section q σ hσ hopen
  let : QuasiCompact W.ι := sectionComponentOpen_quasiCompact_ι q σ hσ hopen hretro
  have hsm : SmoothOfRelativeDimension n (W.ι ≫ q) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (W.ι ≫ q))
  let : SmoothOfRelativeDimension n (W.ι ≫ q) := hsm
  let : Smooth (W.ι ≫ q) := SmoothOfRelativeDimension.smooth n (W.ι ≫ q)
  exact ⟨W, τ, rfl, hτ, hτq, hsm, inferInstance, inferInstance,
    sectionComponentOpen_geometricallyConnected q σ hσ hopen, inferInstance⟩

end AlgebraicGeometry.Scheme
