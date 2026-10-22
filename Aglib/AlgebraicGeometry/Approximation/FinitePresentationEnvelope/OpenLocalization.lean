/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions from localized ring isomorphisms

If a spectral map is an isomorphism on each of a family of target principal
opens, its restriction to the union of their full inverse images is an open
immersion. The actual spectral map and open-subscheme inclusion are retained.

This supplies the geometric locality step shared by Stacks Project, Tags 01Z7
and 01Z9. It requires no finite-type or Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology

universe u v

namespace AlgebraicGeometry.Scheme

/-- Restricting a map to a union of full inverse images preserves local open
immersion certificates over the corresponding target opens. -/
lemma isOpenImmersion_open_comp_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens)
    {ι : Type v} (V : ι → Y.Opens) (hU : U = ⨆ a, f ⁻¹ᵁ V a)
    (hV : ∀ a, IsOpenImmersion (f ∣_ V a)) :
    IsOpenImmersion (U.ι ≫ f) := by
  have hle (a : ι) : f ⁻¹ᵁ V a ≤ U := by
    rw [hU]
    exact le_iSup (fun a ↦ f ⁻¹ᵁ V a) a
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage
  intro x
  have hx : x.1 ∈ ⨆ a, f ⁻¹ᵁ V a := by rw [← hU]; exact x.2
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨V a, ha, ?_⟩
  have : IsOpenImmersion (f ∣_ V a) := hV a
  have : IsOpenImmersion ((f ⁻¹ᵁ V a).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  change IsOpenImmersion (((U.ι ≫ f) ⁻¹ᵁ V a).ι ≫ (U.ι ≫ f))
  rw [Hom.comp_preimage]
  rw [← Category.assoc, ← Opens.isoOfLE_hom_ι (hle a), Category.assoc]
  infer_instance

/-- A ring map induces an open immersion on the union of principal opens
where its actual localized ring maps are bijective. Finiteness of the family
is unnecessary for this geometric locality statement. -/
lemma isOpenImmersion_open_comp_of_awayMap_bijective
    {A R : CommRingCat.{u}} (φ : A ⟶ R) (U : (Spec R).Opens)
    {ι : Type v} (r : ι → A)
    (hU : U = ⨆ a, PrimeSpectrum.basicOpen (φ.hom (r a)))
    (h : ∀ a, Function.Bijective (Localization.awayMap φ.hom (r a))) :
    IsOpenImmersion (U.ι ≫ Spec.map φ) := by
  apply isOpenImmersion_open_comp_of_restrict (Spec.map φ) U
    (fun a ↦ PrimeSpectrum.basicOpen (r a))
  · rw [hU]
    congr 1
  · intro a
    have : IsIso (CommRingCat.ofHom (Localization.awayMap φ.hom (r a))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (h a)
    apply (MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion)
      (SpecMapRestrictBasicOpenIso φ (r a))).mpr
    infer_instance

end AlgebraicGeometry.Scheme
