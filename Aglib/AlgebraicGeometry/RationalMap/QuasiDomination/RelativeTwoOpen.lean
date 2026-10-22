/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.ProtectedOpen
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.TopologicalDensity
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenRestriction
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Relative
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ProtectedOverlap
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.CartesianSupport
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.SupportedGraph

/-!
# Relative quasi-domination preserving a larger open

The target has a concrete relative quasi-affine presentation over an arbitrary
base. Boundary separation places the original graph image over a complementary
open. The relative one-open construction on that open retains its actual
admissible sequence, which extends to the ambient scheme preserving the larger
open. A Cartesian comparison and the supported-graph criterion then give a
closed global graph. Global density follows from actual sequence density, not
from local schematic density or an arbitrary proper morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

private lemma lift_congrHom {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
    (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
    (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
    pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
  subst a'
  subst b'
  simp

/-- Relative two-open quasi-domination by an actual finite admissible sequence.
The explicit graph closedness over `V` is a genuine hypothesis when `U < V`.
The base and modified source are not assumed affine or reduced. -/
theorem exists_relative_twoOpen_quasiDomination
    {X Y P S : Scheme.{u}} [IsNoetherian X]
    (U V : X.Opens) (hUV : U ≤ V) (hU : Dense (U : Set X))
    (p : X ⟶ S) (e : Y ⟶ P) (pP : P ⟶ S)
    [IsImmersion e] [IsAffineHom pP]
    [QuasiCompact (e ≫ pP)] [LocallyOfFiniteType (e ≫ pP)]
    (g : U.toScheme ⟶ Y) (hg : g ≫ (e ≫ pP) = U.ι ≫ p)
    (hclosed : IsClosed ((pullback.fst p (e ≫ pP) ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g hg.symm))) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (D : Scheme.{u}) (d : D ⟶ X')
      (h : D ⟶ Y) (j : U.toScheme ⟶ D) (hw : d ≫ β ≫ p = h ≫ (e ≫ pP)),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      IsOpenImmersion d ∧ DenseRange d ∧
      IsSchemeTheoreticallyDominant j ∧ j ≫ d ≫ β = U.ι ∧ j ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  classical
  let f := e ≫ pP
  let : CompactSpace U.toScheme := by
    change CompactSpace (U : Set X)
    infer_instance
  let : IsNoetherian U.toScheme := ⟨⟩
  let : QuasiCompact f := inferInstance
  let Z := pullback p f
  let p₁ : Z ⟶ X := pullback.fst p f
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p₁
  let : CompactSpace Z := inferInstance
  let : IsNoetherian Z := ⟨⟩
  let γ : U.toScheme ⟶ Z := pullback.lift U.ι g hg.symm
  have hγ : γ ≫ p₁ = U.ι := pullback.lift_fst _ _ _
  let : IsImmersion (γ ≫ p₁) := by rw [hγ]; infer_instance
  let : IsImmersion γ := IsImmersion.of_comp γ p₁
  obtain ⟨I₁, I₂, _, _, hI₂, _, hB, hBV, hsep⟩ :=
    Blowup.exists_canonical_boundary_separation p₁ γ U V hUV
      (by rw [hγ, Scheme.Opens.range_ι]) hclosed
  let B := Blowup.blowupDatum (I₁ ⊔ I₂)
  let W := Blowup.boundaryComplement B.map U V
  let T := W.ι ⁻¹ᵁ B.map ⁻¹ᵁ V
  have hW : W ⊓ B.map ⁻¹ᵁ V = B.map ⁻¹ᵁ U :=
    Blowup.boundaryComplement_inf_preimage B.map U V hUV
  have hKV : (I₁ ⊔ I₂).comap V.ι = ⊤ :=
    Blowup.BlowupDatum.comap_eq_top_of_disjoint V (by
      refine Set.disjoint_left.mpr ?_
      intro x hxV hxK
      rw [IdealSheafData.support_sup] at hxK
      exact (hI₂ hxK.2).2 hxV)
  let : IsProper B.map := hB
  let : IsIso (B.map ∣_ V) := hBV
  let : IsIso (B.map ∣_ U) := B.map.isIso_restrict_of_le hUV
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  let : IsNoetherian B.Y := ⟨⟩
  let E := protectedOverlapIso B.map U V W hW
  have hE : E.hom ≫ U.ι = T.ι ≫ W.ι ≫ B.map :=
    protectedOverlapIso_hom_ι B.map U V W hW
  let gT := E.hom ≫ g
  have hgT : gT ≫ f = T.ι ≫ W.ι ≫ B.map ≫ p := by
    dsimp only [gT]
    rw [Category.assoc, hg, ← Category.assoc E.hom U.ι, hE]
    simp only [Category.assoc]
  let γ₁ := pullback.snd γ (pullback.fst p₁ B.map)
  let r := Blowup.imageToBoundaryComplement B.map (pullback.snd p₁ B.map) γ₁ U V hsep
  have hr : r ≫ W.ι = γ₁.imageι ≫ pullback.snd p₁ B.map :=
    Blowup.imageToBoundaryComplement_ι B.map (pullback.snd p₁ B.map) γ₁ U V hsep
  let EP := (pullbackSymmetry p₁ B.map) ≪≫ pullbackRightPullbackFstIso p f B.map
  have hEP₁ : EP.hom ≫ pullback.fst (B.map ≫ p) f = pullback.snd p₁ B.map := by
    simp [EP, p₁, Category.assoc]
  have hEP₂ : EP.hom ≫ pullback.snd (B.map ≫ p) f =
      pullback.fst p₁ B.map ≫ pullback.snd p f := by
    simp [EP, p₁, Category.assoc]
  let c := γ₁.imageι ≫ EP.hom
  let : IsClosedImmersion c := inferInstance
  have hrc : r ≫ W.ι = c ≫ pullback.fst (B.map ≫ p) f := by
    simpa only [c, Category.assoc, hEP₁] using hr
  let a₁ : T.toScheme ⟶ pullback p₁ B.map :=
    pullback.lift (E.hom ≫ γ) (T.ι ≫ W.ι) (by
      rw [Category.assoc, hγ, hE, Category.assoc])
  let a₀ : T.toScheme ⟶ pullback γ (pullback.fst p₁ B.map) :=
    pullback.lift E.hom a₁ (pullback.lift_fst _ _ _).symm
  let a := a₀ ≫ γ₁.toImage
  have hac : a ≫ γ₁.imageι = a₁ := by
    calc
      a ≫ γ₁.imageι = a₀ ≫ γ₁ := by
        simp only [a, Category.assoc, Scheme.Hom.toImage_imageι]
      _ = a₁ := pullback.lift_snd _ _ _
  have hc₁ : c ≫ pullback.fst (B.map ≫ p) f =
      γ₁.imageι ≫ pullback.snd p₁ B.map := by
    change (γ₁.imageι ≫ EP.hom) ≫ _ = _
    rw [Category.assoc, hEP₁]
  have hc₂ : c ≫ pullback.snd (B.map ≫ p) f =
      γ₁.imageι ≫ pullback.fst p₁ B.map ≫ pullback.snd p f := by
    change (γ₁.imageι ≫ EP.hom) ≫ _ = _
    rw [Category.assoc, hEP₂]
  have ha₁ : a ≫ c ≫ pullback.fst (B.map ≫ p) f = T.ι ≫ W.ι := by
    rw [hc₁, ← Category.assoc, hac]
    exact pullback.lift_snd _ _ _
  have ha₂ : a ≫ c ≫ pullback.snd (B.map ≫ p) f = gT := by
    rw [hc₂, ← Category.assoc a γ₁.imageι, hac]
    calc
      a₁ ≫ pullback.fst p₁ B.map ≫ pullback.snd p f =
          (E.hom ≫ γ) ≫ pullback.snd p f :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ k ≫ pullback.snd p f) (pullback.lift_fst _ _ _))
      _ = E.hom ≫ g := (Category.assoc _ _ _).trans
        (congrArg (fun k ↦ E.hom ≫ k) (pullback.lift_snd U.ι g hg.symm))
  let : CompactSpace W.toScheme := by
    change CompactSpace (W : Set B.Y)
    infer_instance
  let : IsNoetherian W.toScheme := ⟨⟩
  obtain ⟨Q, z, D, d₀, h, jT, hw₀, hseqLocal, _, _, hd₀, _, _, hdj, hjD, hjh, hgraph⟩ :=
    exists_relative_quasiDomination T (W.ι ≫ B.map ≫ p) e pP gT hgT
  obtain ⟨X', β, q, hseq, hsq⟩ :=
    hseqLocal.exists_open_extension W.ι (B.map ⁻¹ᵁ V)
  let : IsOpenImmersion q := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : IsProper β := hseq.isProper
  let : IsIso (β ∣_ B.map ⁻¹ᵁ V) := hseq.restrict_isIso
  let : IsOpenImmersion d₀ := hd₀
  let : IsSchemeTheoreticallyDominant jT := hdj
  let : IsClosedImmersion (pullback.lift d₀ h hw₀) := hgraph
  let j := E.inv ≫ jT
  let d := d₀ ≫ q
  have hbaseQ : z ≫ W.ι ≫ B.map ≫ p = q ≫ β ≫ (B.map ≫ p) := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ B.map ≫ p) hsq.w.symm
  have hw : d ≫ (β ≫ B.map) ≫ p = h ≫ f := by
    dsimp only [d]
    rw [Category.assoc, Category.assoc, ← hbaseQ]
    exact hw₀
  let L := pullback.congrHom hbaseQ (rfl : f = f)
  have hwH : d₀ ≫ (q ≫ β ≫ (B.map ≫ p)) = h ≫ f :=
    (congrArg (fun k ↦ d₀ ≫ k) hbaseQ).symm.trans hw₀
  let H := pullback.lift d₀ h hwH
  have hHeq : H = pullback.lift d₀ h hw₀ ≫ L.hom :=
    lift_congrHom hbaseQ rfl d₀ h hw₀ hwH
  have hH₁ : H ≫ pullback.fst (q ≫ β ≫ (B.map ≫ p)) f = d₀ :=
    pullback.lift_fst _ _ _
  have hH₂ : H ≫ pullback.snd (q ≫ β ≫ (B.map ≫ p)) f = h :=
    pullback.lift_snd _ _ _
  let o := productBaseChangeMap q (β ≫ (B.map ≫ p)) f
  let m := productBaseChangeMap β (B.map ≫ p) f
  let C := pullback c m
  let c' : C ⟶ pullback (β ≫ (B.map ≫ p)) f := pullback.snd c m
  let r' := supportedGraphBaseChangeLiftOfIsPullback W (B.map ≫ p) f c r hrc β q z hsq
  have hr' : r' ≫ o = c' :=
    supportedGraphBaseChangeLiftOfIsPullback_comp W (B.map ≫ p) f c r hrc β q z hsq
  have hcompat : a ≫ c = (jT ≫ H ≫ o) ≫ m := by
    apply pullback.hom_ext
    · simp only [Category.assoc, m, o, productBaseChangeMap_fst,
        productBaseChangeMap_fst_assoc, reassoc_of% hH₁]
      rw [ha₁]
      exact (congrArg (fun k ↦ k ≫ W.ι) hjD.symm).trans
        ((Category.assoc jT (d₀ ≫ z) W.ι).trans
          ((congrArg (fun k ↦ jT ≫ k) (Category.assoc d₀ z W.ι)).trans
            (congrArg (fun k ↦ jT ≫ d₀ ≫ k) hsq.w.symm)))
    · simp only [Category.assoc, m, o, productBaseChangeMap_snd, hH₂]
      exact ha₂.trans hjh.symm
  let a' : T.toScheme ⟶ C := pullback.lift a (jT ≫ H ≫ o) hcompat
  have w : jT ≫ (H ≫ o) = a' ≫ c' := (pullback.lift_snd _ _ _).symm
  let : IsClosedImmersion H := by
    rw [hHeq]
    infer_instance
  let : IsClosedImmersion (H ≫ o) :=
    isClosedImmersion_comp_of_supported_dense_factor o c' r' hr' H jT a' w
  have hjbase : j ≫ d ≫ (β ≫ B.map) = U.ι := by
    dsimp only [j, d]
    simp only [Category.assoc]
    rw [← Category.assoc q β, hsq.w]
    simp only [Category.assoc, reassoc_of% hjD]
    rw [← hE]
    simp
  have hjmap : j ≫ h = g := by
    dsimp only [j]
    rw [Category.assoc, hjh]
    change E.inv ≫ E.hom ≫ g = g
    simp
  have htotal : Blowup.AdmissibleSequence V (β ≫ B.map) :=
    (Blowup.AdmissibleSequence.single B V hKV).comp hseq
  let : IsIso ((β ≫ B.map) ∣_ V) := htotal.restrict_isIso
  let : IsIso ((β ≫ B.map) ∣_ U) := (β ≫ B.map).isIso_restrict_of_le hUV
  have hpreU := htotal.preimage_open_dense U hU
  let K := isPullback_morphismRestrict (β ≫ B.map) U
  let k := K.lift (𝟙 U.toScheme) (j ≫ d)
    (by simpa only [Category.id_comp, Category.assoc] using hjbase.symm)
  have hk₁ : k ≫ ((β ≫ B.map) ⁻¹ᵁ U).ι = j ≫ d := K.lift_snd _ _ _
  have hk₂ : k ≫ ((β ≫ B.map) ∣_ U) = 𝟙 _ := K.lift_fst _ _ _
  have hk : k = inv ((β ≫ B.map) ∣_ U) := by
    apply (cancel_mono ((β ≫ B.map) ∣_ U)).mp
    exact hk₂.trans (IsIso.inv_hom_id ((β ≫ B.map) ∣_ U)).symm
  let : IsIso k := by rw [hk]; infer_instance
  have hjpre : (inv k ≫ j) ≫ d = ((β ≫ B.map) ⁻¹ᵁ U).ι := by
    rw [Category.assoc, ← hk₁, IsIso.inv_hom_id_assoc]
  have hdense : DenseRange d := by
    have hi : DenseRange ((β ≫ B.map) ⁻¹ᵁ U).ι := by
      change Dense (Set.range ((β ≫ B.map) ⁻¹ᵁ U).ι)
      rwa [Scheme.Opens.range_ι]
    apply hi.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨(inv k ≫ j) x, congrArg (fun t ↦ t x) hjpre⟩
  refine ⟨X', β ≫ B.map, D, d, h, j, hw, htotal, inferInstance, inferInstance,
    inferInstance, hdense, inferInstance, hjbase, hjmap, ?_⟩
  let A := pullback.congrHom (Category.assoc β B.map p).symm (rfl : f = f)
  have hwD : d ≫ (β ≫ B.map ≫ p) = h ≫ f := by
    simpa only [Category.assoc] using hw
  have hGraph : pullback.lift d h hwD = H ≫ o := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst d h hwD).trans
        ((Category.assoc H o _).trans
          ((congrArg (fun k ↦ H ≫ k)
            (productBaseChangeMap_fst q (β ≫ B.map ≫ p) f)).trans
            ((Category.assoc H _ q).symm.trans
              (congrArg (fun k ↦ k ≫ q) hH₁)))).symm
    · exact (pullback.lift_snd d h hwD).trans
        ((Category.assoc H o _).trans
          ((congrArg (fun k ↦ H ≫ k)
            (productBaseChangeMap_snd q (β ≫ B.map ≫ p) f)).trans hH₂)).symm
  have he : pullback.lift d h hw = (H ≫ o) ≫ A.hom :=
    (lift_congrHom (Category.assoc β B.map p).symm rfl d h hwD hw).trans
      (congrArg (fun k ↦ k ≫ A.hom) hGraph)
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
