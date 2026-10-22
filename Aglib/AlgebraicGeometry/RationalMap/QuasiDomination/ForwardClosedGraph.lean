/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GeneralRelative
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenLift
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# A forward closed graph from a shared dense open

The first quasi-domination pass provides an actual open model with closed
forward graph. This construction is shared by compactifiability and common
enlargement, and needs no properness of the right-hand ambient model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Construct the forward closed graph while retaining the actual original open
and the protected inverse-image open on the modified ambient model. -/
theorem exists_forward_closedGraph_of_openImmersion
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) (U : X.Opens)
    (c : U.toScheme ⟶ Y) [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (hc : c ≫ pY = U.ι ≫ pX) :
    ∃ (Y₁ : Scheme.{u}) (α : Y₁ ⟶ Y) (V : Scheme.{u}) (v : V ⟶ Y₁)
      (φ : V ⟶ X) (u : U.toScheme ⟶ V) (hφ : φ ≫ pX = v ≫ α ≫ pY),
      Blowup.AdmissibleSequence c.opensRange α ∧ IsProper α ∧
      IsOpenImmersion v ∧ IsOpenImmersion u ∧ IsSchemeTheoreticallyDominant u ∧
      u ≫ φ = U.ι ∧ IsClosedImmersion (pullback.lift φ v hφ) ∧
      Set.range (u ≫ v) = (α ⁻¹ᵁ c.opensRange : Set Y₁) ∧ (u ≫ v) ≫ α = c := by
  let : NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let UY := c.opensRange
  let E := c.isoOpensRange
  let g := E.inv ≫ U.ι
  have hg : g ≫ pX = UY.ι ≫ pY := by
    calc
      g ≫ pX = E.inv ≫ (c ≫ pY) := by
        dsimp only [g]
        rw [Category.assoc, hc]
      _ = UY.ι ≫ pY := by rw [← Category.assoc, c.isoOpensRange_inv_comp]
  have hUY : Dense (UY : Set Y) := c.denseRange
  obtain ⟨Y₁, α, V, v, φ, k, hw, hα, hαp, hαU, hv, _, hk, hkv, hkφ, hgraph⟩ :=
    exists_relative_quasiDomination_oneOpen pY pX UY hUY g hg
  let : IsProper α := hαp
  let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian α
  let : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace α
  let : IsNoetherian Y₁ := ⟨⟩
  let : IsOpenImmersion v := hv
  let : NoetherianSpace V := v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsSchemeTheoreticallyDominant k := hk
  let : IsIso (α ∣_ UY) := hαU
  have hkv' : (k ≫ v) ≫ α = UY.ι := by simpa only [Category.assoc] using hkv
  let : IsOpenImmersion (k ≫ v) :=
    α.isOpenImmersion_of_isIso_restriction UY (k ≫ v) hkv'
  let : IsOpenImmersion k := IsOpenImmersion.of_comp k v
  let u := E.hom ≫ k
  have hu : u ≫ φ = U.ι := by
    simp only [u, Category.assoc, hkφ, g, Iso.hom_inv_id_assoc]
  have hφ : φ ≫ pX = v ≫ (α ≫ pY) := hw.symm
  let : IsClosedImmersion (pullback.lift v φ hw) := hgraph
  let : IsClosedImmersion (pullback.lift φ v hφ) := by
    have he : pullback.lift φ v hφ =
        pullback.lift v φ hw ≫ (pullbackSymmetry (α ≫ pY) pX).hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
        exact (pullback.lift_fst φ v hφ).trans (pullback.lift_snd v φ hw).symm
      · rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
        exact (pullback.lift_snd φ v hφ).trans (pullback.lift_fst v φ hw).symm
    rw [he]
    infer_instance
  have hprotected : (u ≫ v).opensRange = α ⁻¹ᵁ UY := by
    have he : u ≫ v = E.hom ≫ (inv (α ∣_ UY) ≫ (α ⁻¹ᵁ UY).ι) := by
      dsimp only [u]
      rw [Category.assoc, ← α.eq_inv_restrict_comp UY (k ≫ v) hkv']
    let F := E ≪≫ (asIso (α ∣_ UY)).symm
    apply SetLike.coe_injective
    change Set.range (u ≫ v) = (α ⁻¹ᵁ UY : Set Y₁)
    calc
      Set.range (u ≫ v) = Set.range (F.hom ≫ (α ⁻¹ᵁ UY).ι) :=
        congrArg (fun z : U.toScheme ⟶ Y₁ ↦ Set.range z) he
      _ = Set.range (α ⁻¹ᵁ UY).ι := Hom.Range.range_iso_comp F _
      _ = (α ⁻¹ᵁ UY : Set Y₁) := Opens.range_ι _
  refine ⟨Y₁, α, V, v, φ, u, hφ, hα, hαp, hv, inferInstance,
    inferInstance, hu, inferInstance, congrArg SetLike.coe hprotected, ?_⟩
  calc
    (u ≫ v) ≫ α = E.hom ≫ UY.ι := by simp only [u, Category.assoc, hkv]
    _ = c := c.isoOpensRange_hom_ι

end AlgebraicGeometry.Scheme.QuasiDomination
