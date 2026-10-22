/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Refinement
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Density
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphPullback
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphImageLocality
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Dominance
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenHomExt

/-!
# Finite-cover assembly of actual partial graphs

Local admissible sequences are extended to the ambient scheme and refined by
one actual admissible sequence. The local closed graphs are pulled back along
its actual comparisons. Schematic density comes from the globally dense
protected open, not from the comparison maps. The single original graph's
schematic image then has open projection by the local graph criterion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.QuasiDomination

private lemma congrHom_fst {A B S : Scheme.{u}} {f f' : A ⟶ S} {g g' : B ⟶ S}
    (hf : f = f') (hg : g = g') :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f' g' = pullback.fst f g := by
  subst f'
  subst g'
  simp

private lemma congrHom_snd {A B S : Scheme.{u}} {f f' : A ⟶ S} {g g' : B ⟶ S}
    (hf : f = f') (hg : g = g') :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f' g' = pullback.snd f g := by
  subst f'
  subst g'
  simp

/-- Actual closed local graphs on a finite open cover give a global partial
map after an actual common admissible sequence. Its domain is the schematic
image of the single original graph, with open projection to the modified base. -/
theorem exists_quasiDomination_of_finite_cover {X Y S : Scheme.{u}}
    [IsNoetherian X] (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (pX : X ⟶ S) (pY : Y ⟶ S) (g : U.toScheme ⟶ Y)
    (hg : g ≫ pY = U.ι ≫ pX)
    (C : X.OpenCover.{v}) [Finite C.I₀] [∀ i, QuasiCompact (C.f i)]
    (B : C.I₀ → Scheme.{u}) (β₀ : ∀ i, B i ⟶ C.X i)
    (hβ₀ : ∀ i, Blowup.AdmissibleSequence (C.f i ⁻¹ᵁ U) (β₀ i))
    (D : ∀ i, (B i).Opens) (h : ∀ i, (D i).toScheme ⟶ Y)
    (j : ∀ i, (C.f i ⁻¹ᵁ U).toScheme ⟶ (D i).toScheme)
    (hw : ∀ i, (D i).ι ≫ β₀ i ≫ C.f i ≫ pX = h i ≫ pY)
    (hj : ∀ i, j i ≫ (D i).ι ≫ β₀ i = (C.f i ⁻¹ᵁ U).ι)
    (hjh : ∀ i, j i ≫ h i = (C.f i ∣_ U) ≫ g)
    (hclosed : ∀ i, IsClosedImmersion (pullback.lift (D i).ι (h i) (hw i))) :
    ∃ (X' : Scheme.{u}) (β : X' ⟶ X) (E : Scheme.{u}) (d : E ⟶ X')
      (F : E ⟶ Y) (k : U.toScheme ⟶ E) (w : d ≫ β ≫ pX = F ≫ pY),
      Blowup.AdmissibleSequence U β ∧ IsOpenImmersion d ∧
      IsSchemeTheoreticallyDominant d ∧ IsSchemeTheoreticallyDominant k ∧
      k ≫ d ≫ β = U.ι ∧ k ≫ F = g ∧ IsClosedImmersion (pullback.lift d F w) := by
  classical
  let : Fintype C.I₀ := Fintype.ofFinite _
  have hext := fun i ↦ (hβ₀ i).exists_open_extension (C.f i) U
  choose A α m hα hm using hext
  obtain ⟨X', β, a₀, hβ, ha₀⟩ := Blowup.AdmissibleSequence.exists_finite_refinement
    U A α hα Finset.univ
  let a : ∀ i, X' ⟶ A i := fun i ↦ a₀ ⟨i, Finset.mem_univ i⟩
  have ha : ∀ i, a i ≫ α i = β := fun i ↦ ha₀ ⟨i, Finset.mem_univ i⟩
  let : IsProper β := hβ.isProper
  let : IsIso (β ∣_ U) := hβ.restrict_isIso
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace β
  let : IsNoetherian X' := ⟨⟩
  let V := β ⁻¹ᵁ U
  let : IsSchemeTheoreticallyDominant V.ι := hβ.preimage_open_isSchemeTheoreticallyDominant
  let : CompactSpace V.toScheme := by
    change CompactSpace (V : Set X')
    infer_instance
  let : IsNoetherian V.toScheme := ⟨⟩
  let g' := (β ∣_ U) ≫ g
  have hg' : V.ι ≫ (β ≫ pX) = g' ≫ pY := by
    simp only [g', Category.assoc, hg]
    exact (morphismRestrict_ι_assoc β U pX).symm
  let γ := pullback.lift V.ι g' hg'
  let P := pullback (β ≫ pX) pY
  let p : P ⟶ X' := pullback.fst (β ≫ pX) pY
  have hγ : γ ≫ p = V.ι := pullback.lift_fst _ _ _
  let C' := C.pullback₁ β
  let b : ∀ i : C.I₀, C'.X i ⟶ B i := fun i ↦
    (hm i).lift (pullback.fst β (C.f i) ≫ a i) (pullback.snd β (C.f i)) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ pullback.fst β (C.f i) ≫ z) (ha i)).trans
          (pullback.condition (f := β) (g := C.f i))))
  have hb : ∀ i : C.I₀, b i ≫ β₀ i = pullback.snd β (C.f i) := fun i ↦
    (hm i).lift_snd _ _ _
  let E₀ : C.I₀ → Scheme.{u} := fun i ↦ pullback (D i).ι (b i)
  let d₀ : ∀ i, E₀ i ⟶ C'.X i := fun i ↦ pullback.snd (D i).ι (b i)
  let H₀ : ∀ i, E₀ i ⟶ Y := fun i ↦ pullback.fst (D i).ι (b i) ≫ h i
  have hbp : ∀ i : C.I₀, b i ≫ (β₀ i ≫ C.f i ≫ pX) = C'.f i ≫ (β ≫ pX) := by
    intro i
    change b i ≫ (β₀ i ≫ C.f i ≫ pX) =
      pullback.fst β (C.f i) ≫ (β ≫ pX)
    exact (Category.assoc (b i) (β₀ i) (C.f i ≫ pX)).symm.trans
      ((congrArg (fun z ↦ z ≫ C.f i ≫ pX) (hb i)).trans
        ((Category.assoc (pullback.snd β (C.f i)) (C.f i) pX).symm.trans
          ((congrArg (fun z ↦ z ≫ pX) (pullback.condition (f := β) (g := C.f i)).symm).trans
            (Category.assoc _ _ _))))
  let L : ∀ i : C.I₀, pullback (b i ≫ (β₀ i ≫ C.f i ≫ pX)) pY ≅
      pullback p (C'.f i) := fun i ↦
    pullback.congrHom (hbp i) rfl ≪≫
      ((pullbackSymmetry p (C'.f i)) ≪≫
        pullbackRightPullbackFstIso (β ≫ pX) pY (C'.f i)).symm
  let c : ∀ i, E₀ i ⟶ pullback p (C'.f i) := fun i ↦
    baseChangeGraph (D i).ι (h i) (β₀ i ≫ C.f i ≫ pX) pY (hw i) (b i) ≫
      (L i).hom
  have hc : ∀ i, IsClosedImmersion (c i) := by
    intro i
    let : IsClosedImmersion (pullback.lift (D i).ι (h i) (hw i)) := hclosed i
    exact inferInstanceAs (IsClosedImmersion (_ ≫ (L i).hom))
  have hcd : ∀ i, c i ≫ pullback.snd p (C'.f i) = d₀ i := by
    intro i
    simp only [c, L, p, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      pullbackSymmetry_inv_comp_snd, pullbackRightPullbackFstIso_inv_fst,
      congrHom_fst, baseChangeGraph_fst]
    rfl
  have hcy : ∀ i, c i ≫ pullback.fst p (C'.f i) ≫ pullback.snd (β ≫ pX) pY = H₀ i := by
    intro i
    simp only [c, L, p, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      pullbackSymmetry_inv_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_snd,
      congrHom_snd, baseChangeGraph_snd]
    rfl
  let T : C.I₀ → Scheme.{u} := fun i ↦ pullback (C'.f i) V.ι
  let t : ∀ i, T i ⟶ V.toScheme := fun i ↦ pullback.snd (C'.f i) V.ι
  let v : ∀ i, T i ⟶ C'.X i := fun i ↦ pullback.fst (C'.f i) V.ι
  have hv : ∀ i, (t i ≫ (β ∣_ U)) ≫ U.ι =
      (v i ≫ pullback.snd β (C.f i)) ≫ C.f i := by
    intro i
    calc
      (t i ≫ (β ∣_ U)) ≫ U.ι = (t i ≫ V.ι) ≫ β := by
        rw [Category.assoc, morphismRestrict_ι, Category.assoc]
      _ = (v i ≫ C'.f i) ≫ β :=
        congrArg (fun z ↦ z ≫ β) (pullback.condition (f := C'.f i) (g := V.ι)).symm
      _ = (v i ≫ pullback.snd β (C.f i)) ≫ C.f i := by
        change (v i ≫ pullback.fst β (C.f i)) ≫ β = _
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ v i ≫ z) (pullback.condition (f := β) (g := C.f i))).trans
            (Category.assoc _ _ _).symm)
  let rU : ∀ i, T i ⟶ (C.f i ⁻¹ᵁ U).toScheme := fun i ↦
    (isPullback_morphismRestrict (C.f i) U).lift
      (t i ≫ (β ∣_ U)) (v i ≫ pullback.snd β (C.f i)) (hv i)
  have hrU₁ : ∀ i, rU i ≫ (C.f i ∣_ U) = t i ≫ (β ∣_ U) := fun i ↦
    (isPullback_morphismRestrict (C.f i) U).lift_fst _ _ _
  have hrU₂ : ∀ i, rU i ≫ (C.f i ⁻¹ᵁ U).ι = v i ≫ pullback.snd β (C.f i) := fun i ↦
    (isPullback_morphismRestrict (C.f i) U).lift_snd _ _ _
  have he : ∀ i, (rU i ≫ j i) ≫ (D i).ι = v i ≫ b i := by
    intro i
    let : IsIso (β₀ i ∣_ C.f i ⁻¹ᵁ U) := (hβ₀ i).restrict_isIso
    apply Hom.ext_of_isIso_restriction (β₀ i) (C.f i ⁻¹ᵁ U) (rU i)
    · simp only [Category.assoc, hj]
    · rw [Category.assoc, hb, ← hrU₂]
  let r : ∀ i, T i ⟶ E₀ i := fun i ↦ pullback.lift (rU i ≫ j i) (v i) (he i)
  have hrd : ∀ i, r i ≫ d₀ i = v i := fun i ↦ pullback.lift_snd _ _ _
  have hr : ∀ i, r i ≫ c i ≫ pullback.fst p (C'.f i) = t i ≫ γ := by
    intro i
    apply pullback.hom_ext
    · change (r i ≫ c i ≫ pullback.fst p (C'.f i)) ≫ p = (t i ≫ γ) ≫ p
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (c i),
        hcd, ← Category.assoc (r i), hrd, Category.assoc, hγ]
      exact pullback.condition
    · simp only [Category.assoc, hcy, H₀, r, pullback.lift_fst_assoc, hjh,
        ← Category.assoc (rU i), hrU₁]
      exact (congrArg (fun k ↦ t i ≫ k) (pullback.lift_snd V.ι g' hg')).symm
  have hopen : IsOpenImmersion (γ.imageι ≫ p) :=
    isOpenImmersion_image_projection_of_openCover p γ V.ι hγ C'
      T t v (fun i ↦ IsPullback.of_hasPullback (C'.f i) V.ι)
      E₀ d₀ (fun i ↦ inferInstance) c hc hcd r hr hrd
  let d := γ.imageι ≫ p
  let F := γ.imageι ≫ pullback.snd (β ≫ pX) pY
  let k := inv (β ∣_ U) ≫ γ.toImage
  let : IsSchemeTheoreticallyDominant γ.toImage := isSchemeTheoreticallyDominant_toImage γ
  have hd : IsSchemeTheoreticallyDominant d := by
    let : IsSchemeTheoreticallyDominant (γ.toImage ≫ d) := by
      simpa only [d, Hom.toImage_imageι_assoc, hγ] using
        (inferInstance : IsSchemeTheoreticallyDominant V.ι)
    exact IsSchemeTheoreticallyDominant.of_comp_right γ.toImage d
  have w : d ≫ β ≫ pX = F ≫ pY := by
    simpa only [d, F, p, Category.assoc] using
      congrArg (fun z ↦ γ.imageι ≫ z) (pullback.condition (f := β ≫ pX) (g := pY))
  refine ⟨X', β, γ.image, d, F, k, w, hβ, hopen, hd, inferInstance, ?_, ?_, ?_⟩
  · simp only [k, d, Category.assoc, Hom.toImage_imageι_assoc]
    rw [← Category.assoc γ p β, hγ]
    change inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ β = U.ι
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · simp only [k, F, Category.assoc, Hom.toImage_imageι_assoc]
    rw [pullback.lift_snd]
    simp [g']
  · have heq : pullback.lift d F w = γ.imageι := by
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact pullback.lift_snd _ _ _
    rw [heq]
    infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
