/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.General
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Quasi-domination over an arbitrary base

Apply the source-relative theorem to the actual base-changed target. The
protected closed range is transported through the canonical product with
an identity, and the final graph through pullback associativity. Neither
step changes the original map or the admissible modification sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Quasi-domination over an arbitrary base, preserving the specified larger
open and the literal original map. -/
theorem exists_relative_quasiDomination_general
    {X Y S : Scheme.{u}} [IsNoetherian X]
    (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsSeparated pY] [QuasiCompact pY] [LocallyOfFiniteType pY]
    (U V : X.Opens) (hUV : U ≤ V) (hU : Dense (U : Set X))
    (g : U.toScheme ⟶ Y) (hg : g ≫ pY = U.ι ≫ pX)
    (hclosed : IsClosed ((pullback.fst pX pY ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g hg.symm))) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : Scheme.{u}) (d : D ⟶ X')
      (h : D ⟶ Y) (j : U.toScheme ⟶ D) (hw : d ≫ β ≫ pX = h ≫ pY),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      IsOpenImmersion d ∧ DenseRange d ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ d ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  let t := pullback.fst pX pY
  let gloc := pullback.lift U.ι g hg.symm
  have hgloc : gloc ≫ t = U.ι := pullback.lift_fst _ _ _
  let δ : U.toScheme ⟶ pullback (𝟙 X) t :=
    pullback.lift U.ι gloc (by simpa using hgloc.symm)
  let k := pullback.snd (𝟙 X) t
  have H : IsPullback δ (𝟙 U.toScheme) k gloc :=
    IsPullback.of_vert_isIso ⟨by
      simpa only [Category.id_comp] using
        (show δ ≫ k = gloc from pullback.lift_snd _ _ _)⟩
  have hr : Set.range δ = k ⁻¹' Set.range gloc :=
    Scheme.Pullback.Transport.range_eq_preimage_of_isPullback H
  have hkp : k ≫ t = pullback.fst (𝟙 X) t := by
    simpa only [k, Category.comp_id] using
      (pullback.condition (f := 𝟙 X) (g := t)).symm
  let O := pullback.fst (𝟙 X) t ⁻¹ᵁ V
  let kV : O.toScheme → (t ⁻¹ᵁ V).toScheme := fun x => ⟨k x.val, by
    change (k ≫ t) x.val ∈ V
    rw [hkp]
    exact x.property⟩
  have hkV : Continuous kV :=
    (k.continuous.comp continuous_subtype_val).subtype_mk _
  have hc : IsClosed (O.ι ⁻¹' Set.range δ) := by
    have heq : O.ι ⁻¹' Set.range δ =
        kV ⁻¹' ((t ⁻¹ᵁ V).ι ⁻¹' Set.range gloc) := by
      rw [hr]
      rfl
    rw [heq]
    exact hclosed.preimage hkV
  obtain ⟨B, β, D, d, hl, j, hwl, hseq, hβ, hV, hd, hdense, hj, hjd, hjh, hcgraph⟩ :=
    exists_quasiDomination t U V hUV hU gloc hgloc hc
  let h := hl ≫ pullback.snd pX pY
  have hw : d ≫ β ≫ pX = h ≫ pY := by
    calc
      d ≫ β ≫ pX = hl ≫ t ≫ pX := by rw [← Category.assoc, hwl, Category.assoc]
      _ = hl ≫ pullback.snd pX pY ≫ pY := by rw [pullback.condition]
      _ = h ≫ pY := by simp only [h, Category.assoc]
  have hjh' : j ≫ h = g := by
    simp only [h, ← Category.assoc, hjh, gloc, pullback.lift_snd]
  refine ⟨B, β, D, d, h, j, hw, hseq, hβ, hV, hd, hdense, hj, hjd, hjh', ?_⟩
  have heq : pullback.lift d h hw =
      pullback.lift d hl hwl ≫ (pullbackRightPullbackFstIso pX pY β).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
        pullback.lift_fst]
      exact (pullback.lift_fst d hl hwl).symm
    · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
        pullback.lift_snd]
      exact (pullback.lift_snd_assoc d hl hwl (pullback.snd pX pY)).symm
  let : IsClosedImmersion (pullback.lift d hl hwl) := hcgraph
  rw [heq]
  infer_instance

/-- The graph of the original map is closed over its own source open. The
lift through that open is a section of the separated restricted projection. -/
theorem isClosed_graph_over_sourceOpen
    {X Y S : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) [IsSeparated pY]
    (U : X.Opens) (g : U.toScheme ⟶ Y) (hg : g ≫ pY = U.ι ≫ pX) :
    IsClosed ((pullback.fst pX pY ⁻¹ᵁ U).ι ⁻¹'
      Set.range (pullback.lift U.ι g hg.symm)) := by
  let γ := pullback.lift U.ι g hg.symm
  let O := pullback.fst pX pY ⁻¹ᵁ U
  have hr : Set.range γ ⊆ Set.range O.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (γ ≫ pullback.fst pX pY) x ∈ U
    rw [pullback.lift_fst]
    exact x.property
  let l := IsOpenImmersion.lift O.ι γ hr
  have hl : l ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have hs : l ≫ (pullback.fst pX pY ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl,
      pullback.lift_fst, Category.id_comp]
  let : IsClosedImmersion (l ≫ (pullback.fst pX pY ∣_ U)) := by
    rw [hs]
    infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.fst pX pY ∣_ U)
  have H : IsPullback l (𝟙 _) O.ι γ := IsOpenImmersion.isPullback_lift_id γ O.ι hr
  rw [← Scheme.Pullback.Transport.range_eq_preimage_of_isPullback H]
  exact l.isClosedEmbedding.isClosed_range

/-- One-open quasi-domination over an arbitrary base. Closedness over the
protected open is automatic from separatedness of the target. -/
theorem exists_relative_quasiDomination_oneOpen
    {X Y S : Scheme.{u}} [IsNoetherian X]
    (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsSeparated pY] [QuasiCompact pY] [LocallyOfFiniteType pY]
    (U : X.Opens) (hU : Dense (U : Set X))
    (g : U.toScheme ⟶ Y) (hg : g ≫ pY = U.ι ≫ pX) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : Scheme.{u}) (d : D ⟶ X')
      (h : D ⟶ Y) (j : U.toScheme ⟶ D) (hw : d ≫ β ≫ pX = h ≫ pY),
      Blowup.AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      IsOpenImmersion d ∧ DenseRange d ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ d ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) :=
  exists_relative_quasiDomination_general pX pY U U le_rfl hU g hg
    (isClosed_graph_over_sourceOpen pX pY U g hg)

end AlgebraicGeometry.Scheme.QuasiDomination
