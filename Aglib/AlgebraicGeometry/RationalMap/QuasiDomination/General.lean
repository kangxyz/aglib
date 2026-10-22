/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.FiniteTargetCover
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ImageProtectedGraph
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.RelativeTwoOpen
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ClosedGraphComposition
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Quasi-domination for arbitrary separated finite-type targets

Finite affine target charts first make the single original graph-image
projection locally quasi-finite. Zariski's Main Theorem supplies its concrete
relative quasi-affine presentation. The relative two-open construction then
extends the original section, preserving the larger protected open. The
output retains a finite admissible sequence, not an asserted single blowup.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

private theorem relative_of_factorization
    {X Y P S : Scheme.{u}} [IsNoetherian X]
    (U V : X.Opens) (hUV : U ≤ V) (hU : Dense (U : Set X))
    (p : X ⟶ S) (f : Y ⟶ S) (e : Y ⟶ P) (a : P ⟶ S)
    [IsImmersion e] [IsAffineHom a] [QuasiCompact f] [LocallyOfFiniteType f]
    (he : e ≫ a = f) (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι ≫ p)
    (hc : IsClosed ((pullback.fst p f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g hg.symm))) :
    ∃ (Z : Scheme.{u}) (δ : Z ⟶ X) (D : Scheme.{u}) (d : D ⟶ Z)
      (h : D ⟶ Y) (k : U.toScheme ⟶ D) (hw : d ≫ δ ≫ p = h ≫ f),
      Blowup.AdmissibleSequence V δ ∧ IsProper δ ∧ IsIso (δ ∣_ V) ∧
      IsOpenImmersion d ∧ DenseRange d ∧ IsSchemeTheoreticallyDominant k ∧
      k ≫ d ≫ δ = U.ι ∧ k ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  subst f
  exact exists_relative_twoOpen_quasiDomination U V hUV hU p e a g hg hc

/-- Quasi-domination preserving a larger open, for an arbitrary separated
finite-type target over the original Noetherian source. The closedness
hypothesis is exactly the original graph being closed over `V`. -/
theorem exists_quasiDomination
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    (U V : X.Opens) (hUV : U ≤ V) (hU : Dense (U : Set X))
    (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι)
    (hclosed : IsClosed ((pullback.fst (𝟙 X) f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g (by simpa using hg.symm)))) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : Scheme.{u}) (d : D ⟶ X')
      (h : D ⟶ Y) (j : U.toScheme ⟶ D) (hw : d ≫ β = h ≫ f),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      IsOpenImmersion d ∧ DenseRange d ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ d ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  classical
  obtain ⟨B, β, hβ, hqfin⟩ :=
    exists_locallyQuasiFinite_graphImage_modification f U V hUV g hg hclosed
  let : IsProper β := hβ.isProper
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace β
  let : IsNoetherian B := ⟨⟩
  let : IsIso (β ∣_ V) := hβ.restrict_isIso
  let : IsIso (β ∣_ U) := β.isIso_restrict_of_le hUV
  let U' := β ⁻¹ᵁ U
  let V' := β ⁻¹ᵁ V
  let : CompactSpace U'.toScheme := by
    change CompactSpace (U' : Set B)
    infer_instance
  let : IsNoetherian U'.toScheme := ⟨⟩
  let γ := modifiedGraph U f g hg β
  let q := γ.imageι ≫ pullback.fst β f
  let : LocallyQuasiFinite q := hqfin
  have hγ : γ ≫ pullback.fst β f = U'.ι := modifiedGraph_fst U f g hg β
  have hgZ : γ.toImage ≫ q = U'.ι ≫ 𝟙 B := by
    dsimp only [q]
    rw [Hom.toImage_imageι_assoc, hγ, Category.comp_id]
  have hcZ : IsClosed ((pullback.fst (𝟙 B) q ⁻¹ᵁ V').ι ⁻¹'
      Set.range (pullback.lift U'.ι γ.toImage hgZ.symm)) := by
    have heq : pullback.lift U'.ι γ.toImage hgZ.symm =
        imageSectionGraph γ (pullback.fst β f) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, imageSectionGraph_fst, hγ]
      · rw [pullback.lift_snd, imageSectionGraph_snd]
    rw [heq]
    exact isClosed_imageSectionGraph_over γ (pullback.fst β f) V'
      (isClosed_modifiedGraph_over U f g hg β V hclosed)
  obtain ⟨B', α₀, D, d, F, k, w, hα₀, hp, hi, hd, hD, hk, hkd₀, hkF, hc⟩ :=
    relative_of_factorization U' V' (fun _ hx ↦ hUV hx)
      (hβ.preimage_open_dense U hU) (𝟙 B) q q.toNormalization q.fromNormalization
      q.toNormalization_fromNormalization γ.toImage hgZ hcZ
  let α := α₀ ≫ 𝟙 B
  have hα : Blowup.AdmissibleSequence V' α := by
    simpa only [α, Category.comp_id] using hα₀
  have hkd : k ≫ d ≫ α = U'.ι := by
    simpa only [α, Category.comp_id] using hkd₀
  let : IsOpenImmersion d := hd
  let : IsSchemeTheoreticallyDominant k := hk
  let : IsClosedImmersion (pullback.lift d F w) := hc
  let E := asIso (β ∣_ U)
  let j := E.inv ≫ k
  let h := F ≫ γ.imageι ≫ pullback.snd β f
  have hw : d ≫ (α ≫ β) = h ≫ f :=
    graph_comp_closedTarget_over β f γ.imageι α d F w
  have hjd : j ≫ d ≫ (α ≫ β) = U.ι := by
    calc
      j ≫ d ≫ (α ≫ β) = E.inv ≫ (k ≫ d ≫ α) ≫ β := by
        simp only [j, Category.assoc]
      _ = E.inv ≫ U'.ι ≫ β := by rw [hkd]
      _ = U.ι := by
        rw [← morphismRestrict_ι β U]
        exact Iso.inv_hom_id_assoc E U.ι
  have hjh : j ≫ h = g := by
    calc
      j ≫ h = E.inv ≫ (k ≫ F) ≫ γ.imageι ≫ pullback.snd β f := by
        simp only [j, h, Category.assoc]
      _ = E.inv ≫ γ.toImage ≫ γ.imageι ≫ pullback.snd β f := by rw [hkF]
      _ = E.inv ≫ γ ≫ pullback.snd β f := by rw [Hom.toImage_imageι_assoc]
      _ = E.inv ≫ (β ∣_ U) ≫ g := by rw [modifiedGraph_snd]
      _ = g := Iso.inv_hom_id_assoc E g
  have hseq := hβ.comp hα
  refine ⟨B', α ≫ β, D, d, h, j, hw, hseq, hseq.isProper,
    hseq.restrict_isIso, hd, hD, inferInstance, hjd, hjh, ?_⟩
  exact isClosedImmersion_graph_comp_closedTarget β f γ.imageι α d F w hw

end AlgebraicGeometry.Scheme.QuasiDomination
