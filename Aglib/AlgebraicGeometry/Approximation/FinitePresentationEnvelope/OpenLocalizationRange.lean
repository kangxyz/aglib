/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenLocalization

/-!
# Exact principal-open images after restriction of scalars

The native localization isomorphisms identify not only an open immersion,
but its full prescribed image. The original source scheme and actual spectral
map are retained through the native isomorphism onto the open image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Passing through the native isomorphism onto the open image preserves the
original open immersion and its composite with the actual spectral map. -/
theorem isOpenImmersion_comp_of_awayMap_bijective
    {A R : CommRingCat.{u}} {W : Scheme.{u}} (e : W ⟶ Spec R)
    [IsOpenImmersion e] (φ : A ⟶ R) {L : Type u} (r : L → A)
    (he : e.opensRange = ⨆ l, PrimeSpectrum.basicOpen (φ.hom (r l)))
    (hφ : ∀ l, Function.Bijective (Localization.awayMap φ.hom (r l))) :
    IsOpenImmersion (e ≫ Spec.map φ) := by
  have : IsOpenImmersion (e.opensRange.ι ≫ Spec.map φ) :=
    isOpenImmersion_open_comp_of_awayMap_bijective φ e.opensRange r he hφ
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac e e.opensRange.ι (by simp),
    Category.assoc]
  infer_instance

/-- The image after restricting scalars is exactly the prescribed union, not
merely an unspecified open. Surjectivity on each principal chart comes from
the actual localized inclusion isomorphism. -/
theorem opensRange_comp_of_awayMap_bijective
    {A R : CommRingCat.{u}} {W : Scheme.{u}} (e : W ⟶ Spec R)
    [IsOpenImmersion e] (φ : A ⟶ R) {L : Type u} (r : L → A)
    (he : e.opensRange = ⨆ l, PrimeSpectrum.basicOpen (φ.hom (r l)))
    (hφ : ∀ l, Function.Bijective (Localization.awayMap φ.hom (r l))) :
    let := isOpenImmersion_comp_of_awayMap_bijective e φ r he hφ
    (e ≫ Spec.map φ).opensRange = ⨆ l, PrimeSpectrum.basicOpen (r l) := by
  let := isOpenImmersion_comp_of_awayMap_bijective e φ r he hφ
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    have hw : e w ∈ e.opensRange := ⟨w, rfl⟩
    rw [he] at hw
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hw
    exact Opens.mem_iSup.mpr ⟨l, hl⟩
  · intro hx
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hx
    have : IsIso (CommRingCat.ofHom (Localization.awayMap φ.hom (r l))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hφ l)
    have : IsIso (Spec.map φ ∣_ PrimeSpectrum.basicOpen (r l)) :=
      (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
        (SpecMapRestrictBasicOpenIso φ (r l))).mpr inferInstance
    obtain ⟨y, hy⟩ := (Spec.map φ ∣_ PrimeSpectrum.basicOpen (r l)).surjective ⟨x, hl⟩
    have hymem : y.1 ∈ e.opensRange := by
      rw [he]
      exact Opens.mem_iSup.mpr ⟨l, y.2⟩
    obtain ⟨w, hw⟩ := hymem
    refine ⟨w, ?_⟩
    change Spec.map φ (e w) = x
    rw [hw]
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hy

/-- A commuting square of open immersions into spectra is cartesian when
its actual images are the corresponding unions of principal opens. -/
theorem isPullback_of_principal_opensRange
    {A B : CommRingCat.{u}} {Z W : Scheme.{u}} (p : Z ⟶ W)
    (e₀ : Z ⟶ Spec B) (e : W ⟶ Spec A)
    [IsOpenImmersion e₀] [IsOpenImmersion e] (q : A ⟶ B)
    {L : Type u} (r : L → A) (H : e₀ ≫ Spec.map q = p ≫ e)
    (he : e.opensRange = ⨆ l, PrimeSpectrum.basicOpen (r l))
    (he₀ : e₀.opensRange = ⨆ l, PrimeSpectrum.basicOpen (q.hom (r l))) :
    IsPullback p e₀ e (Spec.map q) := by
  apply IsOpenImmersion.isPullback p e₀ e (Spec.map q) H
  rw [he, Hom.preimage_iSup, he₀]
  rfl

end AlgebraicGeometry.Scheme
