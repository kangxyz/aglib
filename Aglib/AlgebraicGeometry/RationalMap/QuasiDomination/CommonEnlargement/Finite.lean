/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.CommonEnlargement
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.OpenBaseChange

/-!
# Finite common enlargements

The result records actual schemes, maps, admissible sequences, and a jointly
surjective family of open charts. At each successor, the modification of the
previous common model is restricted by actual Cartesian open base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Concrete witnesses for a common enlargement of the specified family. -/
structure CommonEnlargementData {ι : Type v} {A S : Scheme.{u}}
    (X : ι → Scheme.{u}) (p : ∀ i, X i ⟶ S) (pA : A ⟶ S)
    (c : ∀ i, A ⟶ X i) [∀ i, IsOpenImmersion (c i)] where
  /-- The common Noetherian model of the family. -/
  M : Scheme.{u}
  /-- The separated, quasi-compact structure morphism to `S`, locally of finite type. -/
  pM : M ⟶ S
  /-- The schematically dense open immersion of `A` into `M` over `S`. -/
  common : A ⟶ M
  noetherian : IsNoetherian M
  separated : IsSeparated pM
  quasiCompact : QuasiCompact pM
  locallyOfFiniteType : LocallyOfFiniteType pM
  common_open : IsOpenImmersion common
  common_dense : IsSchemeTheoreticallyDominant common
  common_over : common ≫ pM = pA
  /-- The source schemes of the admissible modifications of the original models `X i`. -/
  T : ι → Scheme.{u}
  /-- The proper morphisms from `T i` to `X i` given by the admissible sequences. -/
  β : ∀ i, T i ⟶ X i
  /-- The open immersions from `T i` to `M`, whose images jointly cover `M`. -/
  chart : ∀ i, T i ⟶ M
  /-- The schematically dense open immersions lifting `c i` through `β i` and
  `common` through `chart i`. -/
  original : ∀ i, A ⟶ T i
  sequence : ∀ i, Blowup.AdmissibleSequence (c i).opensRange (β i)
  proper : ∀ i, IsProper (β i)
  chart_open : ∀ i, IsOpenImmersion (chart i)
  original_open : ∀ i, IsOpenImmersion (original i)
  original_dense : ∀ i, IsSchemeTheoreticallyDominant (original i)
  chart_over : ∀ i, chart i ≫ pM = β i ≫ p i
  original_base : ∀ i, original i ≫ β i = c i
  original_common : ∀ i, original i ≫ chart i = common
  cover : ∀ m, ∃ i t, chart i t = m

private theorem original_lift_properties {A X T : Scheme.{u}} [IsNoetherian X]
    (c : A ⟶ X) [IsOpenImmersion c] [IsSchemeTheoreticallyDominant c]
    (β : T ⟶ X) (hβ : Blowup.AdmissibleSequence c.opensRange β)
    (t : A ⟶ T) (ht : t ≫ β = c) :
    IsOpenImmersion t ∧ IsSchemeTheoreticallyDominant t ∧
      Set.range t = (β ⁻¹ᵁ c.opensRange : Set T) := by
  let E := c.isoOpensRange
  let : IsIso (β ∣_ c.opensRange) := hβ.restrict_isIso
  let : IsSchemeTheoreticallyDominant c.opensRange.ι := by
    rw [← c.isoOpensRange_inv_comp]
    infer_instance
  let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ c.opensRange).ι :=
    hβ.preimage_open_isSchemeTheoreticallyDominant
  have hs : (E.inv ≫ t) ≫ β = c.opensRange.ι := by
    simpa only [Category.assoc, ht, E] using c.isoOpensRange_inv_comp
  have he : t = E.hom ≫ (inv (β ∣_ c.opensRange) ≫ (β ⁻¹ᵁ c.opensRange).ι) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z ↦ E.hom ≫ z) (β.eq_inv_restrict_comp _ (E.inv ≫ t) hs)
  constructor
  · rw [he]
    infer_instance
  constructor
  · rw [he]
    infer_instance
  · let F := E ≪≫ (asIso (β ∣_ c.opensRange)).symm
    calc
      Set.range t = Set.range (F.hom ≫ (β ⁻¹ᵁ c.opensRange).ι) :=
        congrArg (fun z : A ⟶ T ↦ Set.range z) he
      _ = Set.range (β ⁻¹ᵁ c.opensRange).ι := Hom.Range.range_iso_comp F _
      _ = _ := Opens.range_ι _

private theorem exists_updated_piece
    {A X T M M' : Scheme.{u}} [IsNoetherian X]
    (cX : A ⟶ X) [IsOpenImmersion cX] [IsSchemeTheoreticallyDominant cX]
    (cM : A ⟶ M) [IsOpenImmersion cM]
    (β : T ⟶ X) (hβ : Blowup.AdmissibleSequence cX.opensRange β)
    (e : T ⟶ M) [IsOpenImmersion e] (t : A ⟶ T)
    (htβ : t ≫ β = cX) (hte : t ≫ e = cM)
    (α : M' ⟶ M) (hα : Blowup.AdmissibleSequence cM.opensRange α)
    (tM : A ⟶ M') (htM : tM ≫ α = cM) :
    ∃ (T' : Scheme.{u}) (δ : T' ⟶ T) (j : T' ⟶ M') (t' : A ⟶ T'),
      Blowup.AdmissibleSequence cX.opensRange (δ ≫ β) ∧
      IsPullback j δ α e ∧ t' ≫ δ = t ∧ t' ≫ j = tM := by
  obtain ⟨htopen, _, htrange⟩ := original_lift_properties cX β hβ t htβ
  let : IsOpenImmersion t := htopen
  have hprotected : e ⁻¹ᵁ cM.opensRange = β ⁻¹ᵁ cX.opensRange := by
    apply SetLike.coe_injective
    change e ⁻¹' Set.range cM = (β ⁻¹ᵁ cX.opensRange : Set T)
    rw [← htrange]
    ext x
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, e.isOpenEmbedding.injective ?_⟩
      change (t ≫ e) a = e x
      rw [hte]
      exact ha
    · rintro ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      change cM a = (t ≫ e) a
      rw [hte]
  obtain ⟨T', δ, j, hδ, H⟩ := hα.exists_open_baseChange e
  have hδ' : Blowup.AdmissibleSequence (β ⁻¹ᵁ cX.opensRange) δ := by
    rw [← hprotected]
    exact hδ
  let t' := H.lift tM t (htM.trans hte.symm)
  exact ⟨T', δ, j, t', hβ.comp hδ', H, H.lift_snd _ _ _, H.lift_fst _ _ _⟩

/-- A nonempty finite family of Noetherian separated finite-type models with
one shared schematically dense open has a common enlargement by actual
admissible sequences. The original source and all chart maps are retained. -/
theorem exists_finite_common_enlargement {A S : Scheme.{u}} (n : ℕ)
    (X : Fin (n + 1) → Scheme.{u}) (p : ∀ i, X i ⟶ S) (pA : A ⟶ S)
    (c : ∀ i, A ⟶ X i)
    [∀ i, IsNoetherian (X i)] [∀ i, IsSeparated (p i)]
    [∀ i, QuasiCompact (p i)] [∀ i, LocallyOfFiniteType (p i)]
    [∀ i, IsOpenImmersion (c i)] [∀ i, IsSchemeTheoreticallyDominant (c i)]
    (hc : ∀ i, c i ≫ p i = pA) : Nonempty (CommonEnlargementData X p pA c) := by
  classical
  induction n generalizing pA with
  | zero =>
      let e : ∀ i : Fin 1, X i ⟶ X 0 := fun i ↦ by
        have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst i
        exact 𝟙 _
      have he : ∀ i : Fin 1, c i ≫ e i = c 0 := by
        intro i
        have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst i
        simp [e]
      refine ⟨{
        M := X 0, pM := p 0, common := c 0
        noetherian := inferInstance, separated := inferInstance
        quasiCompact := inferInstance, locallyOfFiniteType := inferInstance
        common_open := inferInstance, common_dense := inferInstance, common_over := hc 0
        T := X, β := fun i ↦ 𝟙 _, chart := e, original := c
        sequence := fun i ↦ .id, proper := fun i ↦ inferInstance
        chart_open := ?_, original_open := fun i ↦ inferInstance
        original_dense := fun i ↦ inferInstance
        chart_over := ?_, original_base := fun i ↦ by simp
        original_common := he, cover := ?_ }⟩
      · intro i
        have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst i
        dsimp [e]
        infer_instance
      · intro i
        have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst i
        simp [e]
      · intro x
        exact ⟨0, x, by simp [e]⟩
  | succ n ih =>
      obtain ⟨E⟩ := ih (fun i ↦ X i.succ) (fun i ↦ p i.succ) pA
        (fun i ↦ c i.succ) (fun i ↦ hc i.succ)
      let : IsNoetherian E.M := E.noetherian
      let : IsSeparated E.pM := E.separated
      let : QuasiCompact E.pM := E.quasiCompact
      let : LocallyOfFiniteType E.pM := E.locallyOfFiniteType
      let : IsOpenImmersion E.common := E.common_open
      let : IsSchemeTheoreticallyDominant E.common := E.common_dense
      let F := E.common.isoOpensRange
      let c₀ := F.inv ≫ c 0
      have hc₀ : c₀ ≫ p 0 = E.common.opensRange.ι ≫ E.pM := by
        calc
          c₀ ≫ p 0 = F.inv ≫ pA := by simp only [c₀, Category.assoc, hc]
          _ = F.inv ≫ E.common ≫ E.pM := by rw [E.common_over]
          _ = E.common.opensRange.ι ≫ E.pM := by
            rw [← Category.assoc, E.common.isoOpensRange_inv_comp]
      let : IsSchemeTheoreticallyDominant E.common.opensRange.ι := by
        rw [← E.common.isoOpensRange_inv_comp]
        infer_instance
      obtain ⟨M', N, Z, α, γ, iM, iN, pZ, sM, sN, hα, hγ, hαp, hγp,
        hiM, hiN, hpZ, hqcZ, hlftZ, hsM, hsN, hdM, hdN, hbM, hbN,
        hsα, hsγ, heq, hcover, hNoeth, hdZ⟩ :=
        exists_common_enlargement_with_dense E.pM (p 0) E.common.opensRange c₀ hc₀
      let : IsOpenImmersion iM := hiM
      let : IsOpenImmersion iN := hiN
      let : IsOpenImmersion sM := hsM
      let : IsOpenImmersion sN := hsN
      let : IsSchemeTheoreticallyDominant (sM ≫ iM) := hdZ
      let tM := F.hom ≫ sM
      let tN := F.hom ≫ sN
      have htM : tM ≫ α = E.common := by
        calc
          tM ≫ α = F.hom ≫ E.common.opensRange.ι := by
            simp only [tM, Category.assoc, hsα]
          _ = E.common := E.common.isoOpensRange_hom_ι
      have htN : tN ≫ γ = c 0 := by
        simp only [tN, Category.assoc, hsγ, c₀, Iso.hom_inv_id_assoc]
      have hγ' : Blowup.AdmissibleSequence (c 0).opensRange γ := by
        simpa only [c₀, Hom.opensRange_comp_of_isIso] using hγ
      let : ∀ i, IsOpenImmersion (E.chart i) := E.chart_open
      have hpieces (i : Fin (n + 1)) :=
        exists_updated_piece (c i.succ) E.common (E.β i) (E.sequence i)
          (E.chart i) (E.original i) (E.original_base i) (E.original_common i)
          α hα tM htM
      choose T' δ j t' hseq H htδ htj using hpieces
      let newT : Fin (n + 2) → Scheme.{u} := Fin.cases N T'
      let newβ : ∀ i, newT i ⟶ X i := Fin.cases γ (fun i ↦ δ i ≫ E.β i)
      let newChart : ∀ i, newT i ⟶ Z := Fin.cases iN (fun i ↦ j i ≫ iM)
      let newOriginal : ∀ i, A ⟶ newT i := Fin.cases tN t'
      have hβseq : ∀ i, Blowup.AdmissibleSequence (c i).opensRange (newβ i) :=
        Fin.cases hγ' hseq
      have hbase : ∀ i, newOriginal i ≫ newβ i = c i := by
        refine Fin.cases htN ?_
        intro i
        change t' i ≫ (δ i ≫ E.β i) = c i.succ
        rw [← Category.assoc, htδ, E.original_base]
      have hprops (i) := original_lift_properties (c i) (newβ i) (hβseq i)
        (newOriginal i) (hbase i)
      let : IsSchemeTheoreticallyDominant (tM ≫ iM) := by
        dsimp only [tM]
        rw [Category.assoc]
        infer_instance
      refine ⟨{
        M := Z, pM := pZ, common := tM ≫ iM
        noetherian := hNoeth, separated := hpZ, quasiCompact := hqcZ
        locallyOfFiniteType := hlftZ, common_open := inferInstance
        common_dense := inferInstance, common_over := ?_
        T := newT, β := newβ, chart := newChart, original := newOriginal
        sequence := hβseq, proper := fun i ↦ (hβseq i).isProper
        chart_open := ?_, original_open := fun i ↦ (hprops i).1
        original_dense := fun i ↦ (hprops i).2.1
        chart_over := ?_, original_base := hbase, original_common := ?_, cover := ?_ }⟩
      · rw [Category.assoc, hbM, ← Category.assoc, htM, E.common_over]
      · refine Fin.cases hiN ?_
        intro i
        let : IsOpenImmersion (E.chart i) := E.chart_open i
        let : IsOpenImmersion (j i) := MorphismProperty.of_isPullback (H i).flip inferInstance
        exact inferInstanceAs (IsOpenImmersion (j i ≫ iM))
      · refine Fin.cases hbN ?_
        intro i
        change (j i ≫ iM) ≫ pZ = (δ i ≫ E.β i) ≫ p i.succ
        rw [Category.assoc, hbM, ← Category.assoc, (H i).w,
          Category.assoc, E.chart_over, Category.assoc]
      · refine Fin.cases ?_ ?_
        · change (F.hom ≫ sN) ≫ iN = (F.hom ≫ sM) ≫ iM
          simpa only [Category.assoc] using congrArg (fun z ↦ F.hom ≫ z) heq.symm
        · intro i
          change t' i ≫ (j i ≫ iM) = tM ≫ iM
          rw [← Category.assoc, htj]
      · intro z
        rcases hcover z with ⟨m, hm⟩ | ⟨x, hx⟩
        · obtain ⟨i, y, hy⟩ := E.cover (α m)
          have hmrange : m ∈ Set.range (j i) := by
            rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback (H i)]
            exact ⟨y, hy⟩
          obtain ⟨x, hx⟩ := hmrange
          exact ⟨i.succ, x, by change iM (j i x) = z; rw [hx, hm]⟩
        · exact ⟨0, x, hx⟩

end AlgebraicGeometry.Scheme.QuasiDomination
