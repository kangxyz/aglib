/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descending a finite principal presentation of a quasi-affine range

The sections and the equality of canonical open ranges descend along the original
cone. No affine hypothesis is imposed on its quasi-affine vertices.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A finite family of global sections lifts through one original cone projection. -/
lemma exists_appTop_π_eq_family_of_isLimit {κ : Type v} [Finite κ]
    (s : κ → Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : κ → Γ(D.obj i, ⊤)), ∀ k, s k = (c.π.app i).appTop (t k) := by
  classical
  let _ := Fintype.ofFinite κ
  choose i t ht using fun k => exists_appTop_π_eq_of_isLimit D c hc (s k)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (k : κ) : j ⟶ i k :=
    (hj (Finset.mem_image_of_mem i (Finset.mem_univ k))).some
  refine ⟨j, fun k => (D.map (q k)).appTop (t k), fun k => ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, c.w]
  exact ht k

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- A finite principal description of the canonical range of a quasi-affine limit
holds at a stage, with every defining function lifting its prescribed original section. -/
lemma Scheme.exists_principal_range_of_isLimit
    [∀ i, IsQuasiAffine (D.obj i)] [IsQuasiAffine c.pt]
    {κ : Type v} [Finite κ] (s : κ → Γ(c.pt, ⊤))
    (hs : c.pt.toSpecΓ.opensRange = ⨆ k, PrimeSpectrum.basicOpen (s k)) :
    ∃ (i : I) (t : κ → Γ(D.obj i, ⊤)),
      (∀ k, s k = (c.π.app i).appTop (t k)) ∧
        (D.obj i).toSpecΓ.opensRange = ⨆ k, PrimeSpectrum.basicOpen (t k) := by
  classical
  have (i : I) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_family_of_isLimit D c hc s
  let E := D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec
  let cE := (Scheme.Γ.rightOp ⋙ Scheme.Spec).mapCone c
  have hΓ : PreservesLimit D Scheme.Γ.rightOp := inferInstance
  have hSpec : PreservesLimit (D ⋙ Scheme.Γ.rightOp) Scheme.Spec := inferInstance
  have hcE : IsLimit cE := isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc
  have {i j : I} (f : i ⟶ j) : IsAffineHom (E.map f) := by
    dsimp [E]
    infer_instance
  let U : (E.obj i).Opens := (D.obj i).toSpecΓ.opensRange
  let V : (E.obj i).Opens := ⨆ k, PrimeSpectrum.basicOpen (t k)
  have hU : IsCompact (U : Set (E.obj i)) :=
    isCompact_range (D.obj i).toSpecΓ.continuous
  have hV : IsCompact (V : Set (E.obj i)) := by
    change IsCompact ((⨆ k, PrimeSpectrum.basicOpen (t k) :
      TopologicalSpace.Opens (PrimeSpectrum Γ(D.obj i, ⊤))) :
        Set (PrimeSpectrum Γ(D.obj i, ⊤)))
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun k => PrimeSpectrum.isCompact_basicOpen (t k)
  have H : cE.π.app i ⁻¹ᵁ U = cE.π.app i ⁻¹ᵁ V := by
    change Spec.map (c.π.app i).appTop ⁻¹ᵁ U =
      Spec.map (c.π.app i).appTop ⁻¹ᵁ V
    rw [show Spec.map (c.π.app i).appTop ⁻¹ᵁ U = c.pt.toSpecΓ.opensRange from
      preimage_opensRange_toSpecΓ (X := c.pt) (c.π.app i), hs]
    change (⨆ k, PrimeSpectrum.basicOpen (s k)) =
      Spec.map (c.π.app i).appTop ⁻¹ᵁ
        (⨆ k, (show (Spec Γ(D.obj i, ⊤)).Opens from PrimeSpectrum.basicOpen (t k)))
    rw [Hom.preimage_iSup]
    congr 1
    funext k
    rw [ht k]
    rfl
  obtain ⟨j, q, hq⟩ := exists_map_preimage_eq_map_preimage E cE hcE hU hV H
  refine ⟨j, fun k => (D.map q).appTop (t k), ?_, ?_⟩
  · intro k
    rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, c.w]
    exact ht k
  · rw [← preimage_opensRange_toSpecΓ (D.map q)]
    change E.map q ⁻¹ᵁ U = ⨆ k, PrimeSpectrum.basicOpen ((D.map q).appTop (t k))
    rw [hq]
    change E.map q ⁻¹ᵁ
      (⨆ k, (show (E.obj i).Opens from PrimeSpectrum.basicOpen (t k))) = _
    rw [Hom.preimage_iSup]
    rfl

end AlgebraicGeometry
