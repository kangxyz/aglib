/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.CompactifiableModification
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenLift
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ForwardClosedGraph

/-!
# Compactifiable modifications from a compactification of the dense open

Both forward and reverse quasi-domination are constructed here. The input is
an actual schematically dense open embedding of the original dense open into
a proper model, not an assumed quasi-domination provider. The output retains
actual admissible sequences on both original models and the original map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- A compactification of the specified dense open yields a compactifiable
actual admissible sequence on the source. No projectivity is asserted. -/
theorem exists_compactifiable_sequence_of_openImmersion
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) [IsProper pY]
    (U : X.Opens) (hU : Dense (U : Set X))
    (c : U.toScheme ⟶ Y) [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (hc : c ≫ pY = U.ι ≫ pX) :
    ∃ (T Yn : Scheme.{u}) (β : T ⟶ X) (γ : Yn ⟶ Y)
      (i : T ⟶ Yn) (t : U.toScheme ⟶ T),
      Blowup.AdmissibleSequence U β ∧
      Blowup.AdmissibleSequence c.opensRange γ ∧
      IsProper β ∧ IsProper γ ∧ IsProper (γ ≫ pY) ∧
      IsOpenImmersion i ∧ IsSchemeTheoreticallyDominant t ∧
      IsSchemeTheoreticallyDominant (t ≫ i) ∧ DenseRange i ∧
      i ≫ γ ≫ pY = β ≫ pX ∧ t ≫ β = U.ι ∧ t ≫ i ≫ γ = c := by
  let : NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let UY := c.opensRange
  let E := c.isoOpensRange
  obtain ⟨Y₁, α, V, v, φ, u, hφ, hα, hαp, hv, huOpen, huDense, hu,
      hgraph, hprotected, huα⟩ :=
    exists_forward_closedGraph_of_openImmersion pX pY U c hc
  let : IsProper α := hαp
  let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian α
  let : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace α
  let : IsNoetherian Y₁ := ⟨⟩
  let : IsOpenImmersion v := hv
  let : NoetherianSpace V := v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsOpenImmersion u := huOpen
  let : IsSchemeTheoreticallyDominant u := huDense
  let : IsClosedImmersion (pullback.lift φ v hφ) := hgraph
  obtain ⟨T, Yn, β, δ, i, t, hβ, hδ, hβp, hδp, _, hi, ht, hibase, htβ, hti⟩ :=
    exists_compactifiable_sequence_of_closedGraph pX (α ≫ pY) U hU φ v hφ u hu
  have hprotected' : (u ≫ v).opensRange = α ⁻¹ᵁ UY :=
    SetLike.coe_injective hprotected
  have hδ' : Blowup.AdmissibleSequence (α ⁻¹ᵁ UY) δ := by
    rw [← hprotected']
    exact hδ
  let γ := δ ≫ α
  have hγ : Blowup.AdmissibleSequence UY γ := hα.comp hδ'
  let : IsProper γ := hγ.isProper
  have hti' : t ≫ i ≫ γ = c := by
    calc
      t ≫ i ≫ γ = (t ≫ i ≫ δ) ≫ α := by simp only [γ, Category.assoc]
      _ = (u ≫ v) ≫ α := congrArg (fun z ↦ z ≫ α) hti
      _ = c := huα
  let : IsIso (γ ∣_ UY) := hγ.restrict_isIso
  let : IsSchemeTheoreticallyDominant UY.ι := by
    rw [← c.isoOpensRange_inv_comp]
    infer_instance
  let : IsSchemeTheoreticallyDominant (γ ⁻¹ᵁ UY).ι :=
    hγ.preimage_open_isSchemeTheoreticallyDominant
  have hs : (E.inv ≫ t ≫ i) ≫ γ = UY.ι := by
    simpa only [Category.assoc, hti', E] using c.isoOpensRange_inv_comp
  have he : t ≫ i = E.hom ≫ (inv (γ ∣_ UY) ≫ (γ ⁻¹ᵁ UY).ι) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z ↦ E.hom ≫ z)
        (γ.eq_inv_restrict_comp UY (E.inv ≫ t ≫ i) hs)
  let : IsSchemeTheoreticallyDominant (t ≫ i) := by
    rw [he]
    infer_instance
  have hidense : DenseRange i :=
    (show DenseRange (i ∘ t) from (t ≫ i).denseRange).of_comp
  refine ⟨T, Yn, β, γ, i, t, hβ, hγ, hβp, inferInstance, inferInstance, hi, ht,
    inferInstance, hidense, ?_, htβ, hti'⟩
  simpa only [γ, Category.assoc] using hibase

end AlgebraicGeometry.Scheme.QuasiDomination
