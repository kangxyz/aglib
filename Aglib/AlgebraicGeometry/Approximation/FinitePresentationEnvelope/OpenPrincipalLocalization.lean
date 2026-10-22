/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Principal localizations of a quasi-compact open in a spectrum

For the literal map from a ring to the global sections of a quasi-compact
open subscheme, every principal open contained in that subscheme induces a
bijective native localization map. The corresponding principal open in the
section spectrum lies in the image of the original affinization. A finite
principal cover retains all these certificates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- The actual affinization is invertible over a basic open whose inverse
image is affine. Quasi-compactness and quasi-separatedness supply its original
section-map isomorphism. -/
theorem isIso_toSpecΓ_restrict_basicOpen {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (r : Γ(X, ⊤))
    (hr : IsAffineOpen (X.basicOpen r)) :
    IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen r) := by
  have : IsAffine (Scheme.Opens.toScheme (X := Spec Γ(X, ⊤))
      (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen r
  apply (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr
  refine ⟨?_, ?_⟩
  · rw [toSpecΓ_preimage_basicOpen]
    exact hr
  · simp only [Opens.map_top, morphismRestrict_app]
    refine IsIso.comp_isIso' ?_ inferInstance
    convert! isIso_ΓSpec_adjunction_unit_app_basicOpen r using 0
    exact congr(IsIso ((ΓSpec.adjunction.unit.app X).app $(by simp)))

namespace OpenPrincipalLocalization

variable (B : CommRingCat.{u}) (U : (Spec B).Opens)

/-- The original ring map to the actual global sections of the open scheme. -/
def sectionMap : B ⟶ Γ(U.toScheme, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ U.ι.appTop

/-- The original open immersion is the composite through its affinization. -/
@[reassoc (attr := simp)]
theorem toSpecΓ_sectionMap :
    U.toScheme.toSpecΓ ≫ Spec.map (sectionMap B U) = U.ι := by
  rw [sectionMap, Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The principal open of the restricted global section is the actual
inverse image of the original ring's principal open. -/
theorem basicOpen_sectionMap (g : B) :
    U.toScheme.basicOpen ((sectionMap B U).hom g) = U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen g := by
  rw [← basicOpen_eq_of_affine g, preimage_basicOpen_top]
  rfl

/-- A principal open contained in the original open is affine there. -/
theorem isAffineOpen_basicOpen_sectionMap (g : B) (hg : PrimeSpectrum.basicOpen g ≤ U) :
    IsAffineOpen (U.toScheme.basicOpen ((sectionMap B U).hom g)) := by
  rw [basicOpen_sectionMap]
  have : IsAffine (Scheme.Opens.toScheme (X := Spec B) (PrimeSpectrum.basicOpen g)) :=
    IsAffineOpen.Spec_basicOpen g
  exact IsAffine.of_isIso (Opens.isoOfLE hg).hom

/-- The restriction of the original inclusion to a contained open is the
canonical native open-restriction isomorphism. -/
theorem isIso_restrict_inclusion (V : (Spec B).Opens) (hV : V ≤ U) :
    IsIso (U.ι ∣_ V) := by
  have he : U.ι ∣_ V = (Opens.isoOfLE hV).hom := by
    apply (cancel_mono V.ι).mp
    simp
  rw [he]
  infer_instance

/-- The native localization map of the original section map is bijective
on every principal open contained in the given quasi-compact open. -/
theorem awayMap_bijective (hU : IsCompact (U : Set (Spec B)))
    (g : B) (hg : PrimeSpectrum.basicOpen g ≤ U) :
    Function.Bijective (Localization.awayMap (sectionMap B U).hom g) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ U.isOpen).mp (.of_quasiSeparatedSpace _)
  have : IsIso (U.toScheme.toSpecΓ ∣_
      PrimeSpectrum.basicOpen ((sectionMap B U).hom g)) :=
    isIso_toSpecΓ_restrict_basicOpen _ (isAffineOpen_basicOpen_sectionMap B U g hg)
  have : IsIso (U.ι ∣_ PrimeSpectrum.basicOpen g) := isIso_restrict_inclusion B U _ hg
  have : IsIso ((U.toScheme.toSpecΓ ≫ Spec.map (sectionMap B U)) ∣_
      PrimeSpectrum.basicOpen g) := by
    rw [toSpecΓ_sectionMap]
    infer_instance
  have : IsIso (U.toScheme.toSpecΓ ∣_
      Spec.map (sectionMap B U) ⁻¹ᵁ PrimeSpectrum.basicOpen g) := by
    rw [SpecMap_preimage_basicOpen]
    infer_instance
  have : IsIso ((U.toScheme.toSpecΓ ∣_
      Spec.map (sectionMap B U) ⁻¹ᵁ PrimeSpectrum.basicOpen g) ≫
      (Spec.map (sectionMap B U) ∣_ PrimeSpectrum.basicOpen g)) := by
    rw [← morphismRestrict_comp]
    infer_instance
  have : IsIso (Spec.map (sectionMap B U) ∣_ PrimeSpectrum.basicOpen g) :=
    IsIso.of_isIso_comp_left
      (U.toScheme.toSpecΓ ∣_ Spec.map (sectionMap B U) ⁻¹ᵁ PrimeSpectrum.basicOpen g) _
  apply (isIso_SpecMap_iff
    (f := CommRingCat.ofHom (Localization.awayMap (sectionMap B U).hom g))).mp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (SpecMapRestrictBasicOpenIso (sectionMap B U) g)).mp inferInstance

/-- The matching principal open of the section spectrum is contained in
the image of the original affinization. -/
theorem basicOpen_le_opensRange (hU : IsCompact (U : Set (Spec B)))
    (g : B) (hg : PrimeSpectrum.basicOpen g ≤ U) :
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
    PrimeSpectrum.basicOpen ((sectionMap B U).hom g) ≤ U.toScheme.toSpecΓ.opensRange := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
  have : IsIso (U.toScheme.toSpecΓ ∣_
      PrimeSpectrum.basicOpen ((sectionMap B U).hom g)) :=
    isIso_toSpecΓ_restrict_basicOpen _ (isAffineOpen_basicOpen_sectionMap B U g hg)
  change PrimeSpectrum.basicOpen ((sectionMap B U).hom g) ≤ U.toScheme.toSpecΓ.opensRange
  intro z hz
  obtain ⟨y, hy⟩ := (U.toScheme.toSpecΓ ∣_
    PrimeSpectrum.basicOpen ((sectionMap B U).hom g)).surjective ⟨z, hz⟩
  refine ⟨y.1, ?_⟩
  simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hy

/-- A principal cover of the original open gives the exact principal cover
of its original affinization image. The index need not be finite. -/
theorem opensRange_eq_iSup_basicOpen (hU : IsCompact (U : Set (Spec B)))
    {ι : Type v} (g : ι → B) (hg : U = ⨆ i, PrimeSpectrum.basicOpen (g i)) :
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
    U.toScheme.toSpecΓ.opensRange =
      ⨆ i, PrimeSpectrum.basicOpen ((sectionMap B U).hom (g i)) := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
  change U.toScheme.toSpecΓ.opensRange =
    ⨆ i, PrimeSpectrum.basicOpen ((sectionMap B U).hom (g i))
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    have hx : U.ι x ∈ ⨆ i, PrimeSpectrum.basicOpen (g i) := by
      rw [← hg]
      exact x.property
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    have hi' : U.toScheme.toSpecΓ x ∈
        Spec.map (sectionMap B U) ⁻¹ᵁ PrimeSpectrum.basicOpen (g i) := by
      change Spec.map (sectionMap B U) (U.toScheme.toSpecΓ x) ∈ PrimeSpectrum.basicOpen (g i)
      simpa only [← Hom.comp_apply, toSpecΓ_sectionMap] using hi
    simpa only [SpecMap_preimage_basicOpen] using hi'
  · refine iSup_le fun i => basicOpen_le_opensRange B U hU (g i) ?_
    rw [hg]
    exact le_iSup (fun j => PrimeSpectrum.basicOpen (g j)) i

/-- A finite principal cover of the original open retains the bijective
localization maps and the corresponding affinization-image certificates. -/
theorem exists_finite_principal_cover (hU : IsCompact (U : Set (Spec B))) :
    let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → B),
      U = ⨆ i, PrimeSpectrum.basicOpen (g i) ∧
      (∀ i, Function.Bijective (Localization.awayMap (sectionMap B U).hom (g i))) ∧
      (∀ i, PrimeSpectrum.basicOpen ((sectionMap B U).hom (g i)) ≤
        U.toScheme.toSpecΓ.opensRange) ∧
      U.toScheme.toSpecΓ.opensRange =
        ⨆ i, PrimeSpectrum.basicOpen ((sectionMap B U).hom (g i)) := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : IsQuasiAffine U.toScheme := IsQuasiAffine.of_isImmersion U.ι
  obtain ⟨ι, hι, g, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  have hle (i : ι) : PrimeSpectrum.basicOpen (g i) ≤ U := by
    rw [hg]
    exact le_iSup (fun j => PrimeSpectrum.basicOpen (g j)) i
  let := hι
  exact ⟨ι, Fintype.ofFinite ι, g, hg, fun i => awayMap_bijective B U hU (g i) (hle i),
    (fun i => basicOpen_le_opensRange B U hU (g i) (hle i)),
    opensRange_eq_iSup_basicOpen B U hU g hg⟩

end OpenPrincipalLocalization
end AlgebraicGeometry.Scheme
