/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.Localization

/-!
# Actual common principal neighborhoods of two affine charts

The native affine communication lemma gives the same open as a principal
open in each affine chart. Their literal localization spectra therefore
have the same range. The original open-immersion lift and full faithfulness
of Spec give an actual ring isomorphism and its exact chart equation.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {A B : CommRingCat.{u}} {X : Scheme.{u}}

private theorem principalChartRange (j : Spec A ⟶ X) [IsOpenImmersion j]
    (f : Γ(X, j ''ᵁ (⊤ : (Spec A).Opens))) :
    let a := (Scheme.ΓSpecIso A).hom ((j.appIso ⊤).hom f)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j).opensRange =
      X.basicOpen f := by
  intro a
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway]
  have hb : (Spec A).basicOpen ((j.appIso ⊤).hom f) = PrimeSpectrum.basicOpen a :=
    basicOpen_eq_of_affine' ((j.appIso ⊤).hom f)
  rw [← hb]
  exact (Scheme.image_basicOpen j ((j.appIso ⊤).hom f)).trans
    (congrArg (fun z => X.basicOpen z) (Iso.hom_inv_id_apply (j.appIso ⊤) f))

/-- An actual scheme isomorphism of spectra has the same actual spectral ring isomorphism. -/
def canonicalSpectralRingIso (e : Spec A ≅ Spec B) : B ≅ A where
  hom := Spec.preimage e.hom
  inv := Spec.preimage e.inv
  hom_inv_id := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, e.inv_hom_id]
  inv_hom_id := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, e.hom_inv_id]

/-- The ring comparison has precisely the original spectral isomorphism as its map. -/
theorem canonicalSpectralRingIso_spec_hom (e : Spec A ≅ Spec B) :
    Spec.map (canonicalSpectralRingIso e).hom = e.hom := Spec.map_preimage e.hom

/-- The common neighborhood uses literal principal localization rings, an actual ring
isomorphism, equality of the original chart arrows and an actual point over the chosen point. -/
theorem exists_canonicalCommonPrincipalNeighborhood
    (j : Spec A ⟶ X) (k : Spec B ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (x : X) (hxj : x ∈ j.opensRange) (hxk : x ∈ k.opensRange) :
    ∃ (a : A) (b : B)
      (e : CommRingCat.of (Localization.Away b) ≅ CommRingCat.of (Localization.Away a))
      (z : Spec (CommRingCat.of (Localization.Away a))),
      Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ k =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j ∧
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j) z = x := by
  let U := j ''ᵁ (⊤ : (Spec A).Opens)
  let V := k ''ᵁ (⊤ : (Spec B).Opens)
  have hU : IsAffineOpen U := (isAffineOpen_top (Spec A)).image_of_isOpenImmersion j
  have hV : IsAffineOpen V := (isAffineOpen_top (Spec B)).image_of_isOpenImmersion k
  have hx : x ∈ U ⊓ V := by
    change x ∈ U ∧ x ∈ V
    simpa only [U, V, Scheme.Hom.image_top_eq_opensRange] using And.intro hxj hxk
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x hx
  let a := (Scheme.ΓSpecIso A).hom ((j.appIso ⊤).hom f)
  let b := (Scheme.ΓSpecIso B).hom ((k.appIso ⊤).hom g)
  let j' := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j
  let k' := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ k
  have hj : j'.opensRange = X.basicOpen f := principalChartRange j f
  have hk : k'.opensRange = X.basicOpen g := principalChartRange k g
  have hrange : Set.range j' = Set.range k' :=
    TopologicalSpace.Opens.ext_iff.mp (hj.trans (hfg.trans hk.symm))
  let E := IsOpenImmersion.isoOfRangeEq j' k' hrange
  let e := canonicalSpectralRingIso E
  have he : Spec.map e.hom = E.hom := Spec.map_preimage E.hom
  have hpoint : x ∈ Set.range j' := by
    change x ∈ j'.opensRange
    exact hj.symm ▸ hxf
  obtain ⟨z, hz⟩ := hpoint
  refine ⟨a, b, e, z, ?_, hz⟩
  change Spec.map e.hom ≫ k' = j'
  exact (congrArg (fun t => t ≫ k') he).trans
    (IsOpenImmersion.isoOfRangeEq_hom_fac j' k' hrange)

end AlgebraicGeometry.Scheme.Modules
