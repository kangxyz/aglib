/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ForwardClosedGraph
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ReverseExtension
public import Aglib.AlgebraicGeometry.Gluing.SeparatedModification
public import Aglib.AlgebraicGeometry.Gluing.SchematicDensity.Pushout
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Density

/-!
# A common separated enlargement of two models

Two actual quasi-domination passes and reverse sequence extension give models
which glue along their actual open overlap. Both original modification sequences
and the literal common open are retained. No projectivity or global properness
of the glued structure morphism is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Two Noetherian finite-type separated models sharing a schematically dense
open have actual admissible modifications in a common separated finite-type
model. The two open images cover that model. -/
theorem exists_common_enlargement_with_dense
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) [IsSeparated pY] [QuasiCompact pY] [LocallyOfFiniteType pY]
    (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (c : U.toScheme ⟶ Y) [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (hc : c ≫ pY = U.ι ≫ pX) :
    ∃ (T Yn Z : Scheme.{u}) (β : T ⟶ X) (γ : Yn ⟶ Y)
      (iX : T ⟶ Z) (iY : Yn ⟶ Z) (pZ : Z ⟶ S)
      (tX : U.toScheme ⟶ T) (tY : U.toScheme ⟶ Yn),
      Blowup.AdmissibleSequence U β ∧ Blowup.AdmissibleSequence c.opensRange γ ∧
      IsProper β ∧ IsProper γ ∧ IsOpenImmersion iX ∧ IsOpenImmersion iY ∧
      IsSeparated pZ ∧ QuasiCompact pZ ∧ LocallyOfFiniteType pZ ∧
      IsOpenImmersion tX ∧ IsOpenImmersion tY ∧
      IsSchemeTheoreticallyDominant tX ∧ IsSchemeTheoreticallyDominant tY ∧
      iX ≫ pZ = β ≫ pX ∧ iY ≫ pZ = γ ≫ pY ∧
      tX ≫ β = U.ι ∧ tY ≫ γ = c ∧ tX ≫ iX = tY ≫ iY ∧
      (∀ z, (∃ x, iX x = z) ∨ ∃ y, iY y = z) ∧
      IsNoetherian Z ∧ IsSchemeTheoreticallyDominant (tX ≫ iX) := by
  let : NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hU : Dense (U : Set X) := by
    have h : Dense (Set.range U.ι) := U.ι.denseRange
    rwa [Opens.range_ι] at h
  obtain ⟨Y₁, α, V, v, φ, u, hφ, hα, hαp, hv, huopen, hudense,
      hu, hgraph, hprotected, huα⟩ :=
    exists_forward_closedGraph_of_openImmersion pX pY U c hc
  let : IsProper α := hαp
  let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian α
  let : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace α
  let : IsNoetherian Y₁ := ⟨⟩
  let : IsOpenImmersion v := hv
  let : NoetherianSpace V := v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsOpenImmersion u := huopen
  let : IsSchemeTheoreticallyDominant u := hudense
  have hprotectedOpens : (u ≫ v).opensRange = α ⁻¹ᵁ c.opensRange :=
    SetLike.coe_injective hprotected
  let : IsClosedImmersion (pullback.lift φ v hφ) := hgraph
  let : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType
        (pullback.lift φ v hφ ≫ pullback.fst pX (α ≫ pY)) := inferInstance
    simpa only [pullback.lift_fst] using this
  have huS : u ≫ (v ≫ α ≫ pY) = U.ι ≫ pX := by
    rw [← hφ, ← Category.assoc, hu]
  obtain ⟨T, β, W, j, ψ, k, wS, hβ, hβp, hβU, hj, _, hk, hkj, hkψ, hcW⟩ :=
    exists_relative_quasiDomination_oneOpen pX (v ≫ α ≫ pY) U hU u huS
  let : IsProper β := hβp
  let : IsOpenImmersion j := hj
  let : IsSchemeTheoreticallyDominant k := hk
  let : IsClosedImmersion (pullback.lift j ψ wS) := hcW
  obtain ⟨Yn, δ, r, hδ, hr, hopen, _, _, hcY⟩ :=
    exists_reverse_open_extension U β hβ pX (α ≫ pY) φ v hφ u hu
      j ψ wS k hkj hkψ
  let : IsOpenImmersion r := hopen
  let : IsProper δ := hδ.isProper
  have hδ' : Blowup.AdmissibleSequence (α ⁻¹ᵁ c.opensRange) δ := by
    rw [← hprotectedOpens]
    exact hδ
  let γ := δ ≫ α
  have hγ : Blowup.AdmissibleSequence c.opensRange γ := hα.comp hδ'
  let : IsProper γ := hγ.isProper
  have hglue : j ≫ (β ≫ pX) = (r ≫ δ) ≫ (α ≫ pY) := by
    rw [hr.w]
    exact wS.trans (Category.assoc ψ v (α ≫ pY)).symm
  let : IsClosedImmersion (pullback.lift j (r ≫ δ) hglue) := by
    simpa only [hr.w] using hcY
  let Z := pushout j r
  let pZ : Z ⟶ S :=
    pushout.desc (β ≫ pX) (δ ≫ α ≫ pY) (hglue.trans (Category.assoc _ _ _))
  let : IsSeparated pZ :=
    SeparatedGluing.separated_desc_of_closed_composite_graph j r δ
      (β ≫ pX) (α ≫ pY) hglue
  let tX := k ≫ j
  let tY := k ≫ r
  have htX : tX ≫ β = U.ι := by simpa only [tX, Category.assoc] using hkj
  have htY : tY ≫ γ = c := by
    calc
      tY ≫ γ = (k ≫ ψ ≫ v) ≫ α := by
        simpa only [tY, γ, Category.assoc] using
          congrArg (fun z ↦ k ≫ z ≫ α) hr.w
      _ = (u ≫ v) ≫ α := by rw [← Category.assoc k ψ v, hkψ]
      _ = c := huα
  let : IsIso (β ∣_ U) := hβU
  let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι :=
    hβ.preimage_open_isSchemeTheoreticallyDominant
  let : IsOpenImmersion tX := β.isOpenImmersion_of_isIso_restriction U tX htX
  let : IsSchemeTheoreticallyDominant tX := by
    rw [β.eq_inv_restrict_comp U tX htX]
    infer_instance
  let E := c.isoOpensRange
  let : IsIso (γ ∣_ c.opensRange) := hγ.restrict_isIso
  let : IsSchemeTheoreticallyDominant c.opensRange.ι := by
    rw [← c.isoOpensRange_inv_comp]
    infer_instance
  let : IsSchemeTheoreticallyDominant (γ ⁻¹ᵁ c.opensRange).ι :=
    hγ.preimage_open_isSchemeTheoreticallyDominant
  have hs : (E.inv ≫ tY) ≫ γ = c.opensRange.ι := by
    simpa only [Category.assoc, htY, E] using c.isoOpensRange_inv_comp
  have htYeq : tY = E.hom ≫
      (inv (γ ∣_ c.opensRange) ≫ (γ ⁻¹ᵁ c.opensRange).ι) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z ↦ E.hom ≫ z) (γ.eq_inv_restrict_comp _ (E.inv ≫ tY) hs)
  let : IsOpenImmersion tY := by rw [htYeq]; infer_instance
  let : IsSchemeTheoreticallyDominant tY := by rw [htYeq]; infer_instance
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace β
  let : IsLocallyNoetherian Yn := LocallyOfFiniteType.isLocallyNoetherian γ
  let : CompactSpace Yn := QuasiCompact.compactSpace_of_compactSpace γ
  let C := OpenNormalizationGluing.twoChartCover j r
  let : IsLocallyNoetherian Z := (isLocallyNoetherian_iff_openCover C).mpr (by
    intro b
    cases b <;> dsimp [C, OpenNormalizationGluing.twoChartCover] <;> infer_instance)
  let : CompactSpace Z := openPushout_compactSpace j r
  let : IsNoetherian Z := ⟨⟩
  let : LocallyOfFiniteType pZ := by
    let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) C
    intro b
    cases b
    · change LocallyOfFiniteType (pushout.inl j r ≫ pZ)
      rw [pushout.inl_desc]
      infer_instance
    · change LocallyOfFiniteType (pushout.inr j r ≫ pZ)
      rw [pushout.inr_desc]
      infer_instance
  let : IsSchemeTheoreticallyDominant r :=
    IsSchemeTheoreticallyDominant.of_comp_right k r
  let : IsSchemeTheoreticallyDominant (pushout.inl j r) :=
    pushout_inl_isSchemeTheoreticallyDominant j r
  refine ⟨T, Yn, Z, β, γ, pushout.inl j r, pushout.inr j r, pZ, tX, tY,
    hβ, hγ, hβp, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, pushout.inl_desc _ _ _, ?_, htX, htY, ?_,
    openPushout_covered j r, inferInstance, inferInstance⟩
  · simpa only [γ, Category.assoc] using
      (pushout.inr_desc (β ≫ pX) (δ ≫ α ≫ pY)
        (hglue.trans (Category.assoc r δ (α ≫ pY))))
  · exact (Category.assoc k j _).trans
      ((congrArg (fun z ↦ k ≫ z) (pushout.condition (f := j) (g := r))).trans
        (Category.assoc k r _).symm)

/-- Two Noetherian finite-type separated models sharing a schematically dense
open have actual admissible modifications in a common separated finite-type
model. The two open images cover that model. -/
theorem exists_common_enlargement
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) [IsSeparated pY] [QuasiCompact pY] [LocallyOfFiniteType pY]
    (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (c : U.toScheme ⟶ Y) [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (hc : c ≫ pY = U.ι ≫ pX) :
    ∃ (T Yn Z : Scheme.{u}) (β : T ⟶ X) (γ : Yn ⟶ Y)
      (iX : T ⟶ Z) (iY : Yn ⟶ Z) (pZ : Z ⟶ S)
      (tX : U.toScheme ⟶ T) (tY : U.toScheme ⟶ Yn),
      Blowup.AdmissibleSequence U β ∧ Blowup.AdmissibleSequence c.opensRange γ ∧
      IsProper β ∧ IsProper γ ∧ IsOpenImmersion iX ∧ IsOpenImmersion iY ∧
      IsSeparated pZ ∧ QuasiCompact pZ ∧ LocallyOfFiniteType pZ ∧
      IsOpenImmersion tX ∧ IsOpenImmersion tY ∧
      IsSchemeTheoreticallyDominant tX ∧ IsSchemeTheoreticallyDominant tY ∧
      iX ≫ pZ = β ≫ pX ∧ iY ≫ pZ = γ ≫ pY ∧
      tX ≫ β = U.ι ∧ tY ≫ γ = c ∧ tX ≫ iX = tY ≫ iY ∧
      (∀ z, (∃ x, iX x = z) ∨ ∃ y, iY y = z) := by
  obtain ⟨T, Yn, Z, β, γ, iX, iY, pZ, tX, tY, hβ, hγ, hβp, hγp,
    hiX, hiY, hpZ, hqc, hlft, htX, htY, hdX, hdY, hbX, hbY,
    htx, hty, he, hcover, _, _⟩ :=
    exists_common_enlargement_with_dense pX pY U c hc
  exact ⟨T, Yn, Z, β, γ, iX, iY, pZ, tX, tY, hβ, hγ, hβp, hγp,
    hiX, hiY, hpZ, hqc, hlft, htX, htY, hdX, hdY, hbX, hbY, htx, hty, he, hcover⟩

end AlgebraicGeometry.Scheme.QuasiDomination
