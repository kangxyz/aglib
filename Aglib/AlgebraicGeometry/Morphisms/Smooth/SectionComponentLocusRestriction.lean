/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusOpen

/-! # Restricting to the original section-component locus

When the uniquely defined original locus is open, its actual open subscheme
has the original lifted section and geometrically connected fibres. The
Noetherian affine-base consumer supplies this openness and retrocompactness
from the proved locus theorem, not from a factorization certificate.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- The actual open subscheme of the original section-component locus. -/
def sectionComponentOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (hopen : IsOpen (sectionComponentLocus f σ hσ)) : X.Opens :=
  ⟨sectionComponentLocus f σ hσ, hopen⟩

/-- The original section factors through its actual open component locus. -/
theorem exists_sectionComponentOpen_section {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (hopen : IsOpen (sectionComponentLocus f σ hσ)) :
    ∃ τ : S ⟶ (sectionComponentOpen f σ hσ hopen).toScheme,
      τ ≫ (sectionComponentOpen f σ hσ hopen).ι = σ ∧
      τ ≫ ((sectionComponentOpen f σ hσ hopen).ι ≫ f) = 𝟙 _ := by
  let W := sectionComponentOpen f σ hσ hopen
  have hrange : Set.range σ ⊆ Set.range W.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    exact (section_point_mem_sectionComponentLocus_iff f σ σ hσ hσ s).mpr
      mem_connectedComponent
  let τ := IsOpenImmersion.lift W.ι σ hrange
  have hτ : τ ≫ W.ι = σ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨τ, hτ, ?_⟩
  rw [← Category.assoc, hτ, hσ]

/-- The actual open component locus has geometrically connected fibres.
Only openness of this particular locus is supplied. -/
theorem sectionComponentOpen_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (hopen : IsOpen (sectionComponentLocus f σ hσ)) :
    GeometricallyConnected ((sectionComponentOpen f σ hσ hopen).ι ≫ f) := by
  let W := sectionComponentOpen f σ hσ hopen
  constructor
  intro K _ b Z z₁ z₂ H
  let Y : Scheme.{u} := pullback f b
  let a : Y ⟶ X := pullback.fst f b
  let q : Y ⟶ Spec (.of K) := pullback.snd f b
  let τ : Spec (.of K) ⟶ Y := pullback.lift (b ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hτq : τ ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hτa : τ ≫ a = b ≫ σ := pullback.lift_fst _ _ _
  let T := a ⁻¹ᵁ W
  have hT : (T : Set Y) = connectedComponent (τ (IsLocalRing.closedPoint K)) := by
    change a ⁻¹' sectionComponentLocus f σ hσ = _
    rw [sectionComponentLocus_preimage_of_isPullback f a q b
      (.of_hasPullback f b) σ hσ τ hτq hτa,
      sectionComponentLocus_eq_connectedComponent_of_field K q τ hτq]
  have hc : _root_.IsConnected (T : Set Y) := by
    rw [hT]
    exact isConnected_connectedComponent
  let : ConnectedSpace T.toScheme := isConnected_iff_connectedSpace.mp hc
  have HT : IsPullback (a ∣_ W) (T.ι ≫ q) (W.ι ≫ f) b :=
    (isPullback_morphismRestrict a W).paste_vert (.of_hasPullback f b)
  let e : Z ≅ T.toScheme := H.isoPullback ≪≫ HT.isoPullback.symm
  exact e.hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Retrocompactness of the original locus gives quasi-compactness of its
actual open inclusion, without a Noetherian hypothesis. -/
theorem sectionComponentOpen_quasiCompact_ι
    {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (hopen : IsOpen (sectionComponentLocus f σ hσ))
    (hretro : IsRetrocompact (sectionComponentLocus f σ hσ)) :
    QuasiCompact (sectionComponentOpen f σ hσ hopen).ι := by
  let W := sectionComponentOpen f σ hσ hopen
  constructor
  intro U hU hc
  apply W.ι.isEmbedding.isCompact_iff.mpr
  rw [Set.image_preimage_eq_inter_range, Opens.range_ι, Set.inter_comm]
  exact hretro hc hU

/-- Over the original Noetherian affine base the proved openness theorem
supplies the actual geometrically connected quasi-compact restriction and
both original section triangles. This is not arbitrary-base etale factorization. -/
theorem exists_noetherian_sectionComponent_restriction
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    ∃ (W : X.Opens) (τ : Spec (.of R) ⟶ W.toScheme),
      (W : Set X) = sectionComponentLocus f σ hσ ∧
      τ ≫ W.ι = σ ∧ τ ≫ (W.ι ≫ f) = 𝟙 _ ∧
      GeometricallyConnected (W.ι ≫ f) ∧ QuasiCompact (W.ι ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨hopen, hretro⟩ := sectionComponentLocus_isOpen_isRetrocompact R f n σ hσ
  obtain ⟨τ, hτ, hτf⟩ := exists_sectionComponentOpen_section f σ hσ hopen
  let W := sectionComponentOpen f σ hσ hopen
  let : QuasiCompact W.ι := sectionComponentOpen_quasiCompact_ι f σ hσ hopen hretro
  exact ⟨W, τ, rfl, hτ, hτf,
    sectionComponentOpen_geometricallyConnected f σ hσ hopen, inferInstance⟩

end AlgebraicGeometry.Scheme
