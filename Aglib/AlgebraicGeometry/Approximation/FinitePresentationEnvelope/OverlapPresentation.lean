/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiniteSections

/-!
# Principal presentations of quasi-affine overlaps at a finite stage

A specified finite principal-open presentation of the original affinization
image descends to a stage of a quasi-affine inverse system. Both the original
sections and the exact open image are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite principal presentation of the original quasi-affine image lifts
to an identical principal presentation of an actual stage image. -/
theorem exists_principal_image_at_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, IsQuasiAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) [IsQuasiAffine c.pt]
    {J : Type v} [Finite J] (r : J → Γ(c.pt, ⊤))
    (hr : c.pt.toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (r j)) :
    ∃ (i : I) (t : J → Γ(D.obj i, ⊤)),
      (∀ j, (c.π.app i).appTop (t j) = r j) ∧
      (D.obj i).toSpecΓ.opensRange = ⨆ j, PrimeSpectrum.basicOpen (t j) := by
  have (i : I) : CompactSpace (D.obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace (D.obj i) := inferInstance
  have (i : I) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  obtain ⟨i, t, ht⟩ := Scheme.exists_finite_sections_at_stage D c hc r
  let E := D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec
  let d := (Scheme.Γ.rightOp ⋙ Scheme.Spec).mapCone c
  have hd : IsLimit d := isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc
  have {i j : I} (g : i ⟶ j) : IsAffineHom (E.map g) := by
    change IsAffineHom (Spec.map (D.map g).appTop)
    infer_instance
  let U : (E.obj i).Opens := ⨆ j, PrimeSpectrum.basicOpen (t j)
  let V : (E.obj i).Opens := (D.obj i).toSpecΓ.opensRange
  have hU : IsCompact (U : Set (E.obj i)) := by
    change IsCompact (((⨆ j, PrimeSpectrum.basicOpen (t j)) :
      (Spec Γ(D.obj i, ⊤)).Opens) : Set (Spec Γ(D.obj i, ⊤)))
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun j ↦ (IsAffineOpen.Spec_basicOpen (t j)).isCompact
  have hV : IsCompact (V : Set (E.obj i)) := by
    exact isCompact_range (D.obj i).toSpecΓ.continuous
  have he : d.π.app i ⁻¹ᵁ U = d.π.app i ⁻¹ᵁ V := by
    dsimp only [U, V]
    change Spec.map (c.π.app i).appTop ⁻¹ᵁ (⨆ j, PrimeSpectrum.basicOpen (t j)) =
      Spec.map (c.π.app i).appTop ⁻¹ᵁ (D.obj i).toSpecΓ.opensRange
    rw [Scheme.preimage_opensRange_toSpecΓ (X := c.pt) (c.π.app i)]
    rw [Hom.preimage_iSup]
    change (⨆ j, PrimeSpectrum.basicOpen ((c.π.app i).appTop (t j))) =
      c.pt.toSpecΓ.opensRange
    simpa only [ht] using hr.symm
  obtain ⟨k, g, hg⟩ := AlgebraicGeometry.exists_map_preimage_eq_map_preimage E d hd hU hV he
  refine ⟨k, fun j ↦ (D.map g).appTop (t j), ?_, ?_⟩
  · intro j
    rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, c.w]
    exact ht j
  · dsimp only [U, V] at hg
    change Spec.map (D.map g).appTop ⁻¹ᵁ (⨆ j, PrimeSpectrum.basicOpen (t j)) =
      Spec.map (D.map g).appTop ⁻¹ᵁ (D.obj i).toSpecΓ.opensRange at hg
    rw [Scheme.preimage_opensRange_toSpecΓ] at hg
    rw [Hom.preimage_iSup] at hg
    change (⨆ j, PrimeSpectrum.basicOpen ((D.map g).appTop (t j))) =
      (D.obj k).toSpecΓ.opensRange at hg
    exact hg.symm

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
