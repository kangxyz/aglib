/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompleteAffineFactorizationBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionGeometricReflection
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalModificationComparisonBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletionBaseChange
public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.BaseChangeRestriction

/-! # One exceptional bound on the original affine modification comparison

The base completion is used only to algebraize the pulled formal source.
Actual adjunction and proper pushforward base change identify the specified
comparison there. Reflection is through the original finite-stage units,
not faithful flatness of completion.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  (I : Ideal B) {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p]
  (F : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) I))
  (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p (𝟙 (Spec B)) I).obj F ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) I)).obj G)

/-- Transport a bound through the specified three-factor composite before
specializing any formal completion or native mate. -/
theorem defectsKilled_of_originalComposite
    {Z : Scheme.{u}} [IsLocallyNoetherian Z] {J E : Z.IdealSheafData}
    {M H K N : AdicSystem Z J} {t : ℕ}
    (α : M ⟶ H) (e : H ≅ K) (d : K ≅ N) (k : K ⟶ N)
    (hk : d.hom = k) (ψ : M ⟶ N)
    (hψ : ψ = α ≫ e.hom ≫ k) (h : AdicSystem.DefectsKilled E t ψ) :
    AdicSystem.DefectsKilled E t α := by
  apply h.of_iso_square (Iso.refl M) (e ≪≫ d)
  simpa only [Iso.refl_hom, Iso.trans_hom, Category.id_comp, hk] using hψ.symm

/-- The original affine comparison has a single positive exceptional bound
at every formal stage, without any completeness hypothesis on the affine base. -/
theorem affineModificationComparison_hasBoundedDefects
    (K : (Spec B).IdealSheafData) (U : (Spec B).Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set (Spec B))ᶜ ⊆ K.support) :
    AdicSystem.HasBoundedDefects K (affineModificationComparison p I F G β.hom) := by
  let := AdicCompletion.isNoetherianRing B I
  let S := CommRingCat.of (AdicCompletion I B)
  let φ : B ⟶ S := CommRingCat.ofHom (algebraMap B (AdicCompletion I B))
  let w := Spec.map φ
  let a := Limits.pullback.fst p w
  let b := Limits.pullback.snd p w
  let h := IsPullback.of_hasPullback p w
  let α := affineModificationComparison p I F G β.hom
  let F' := (baseIdealPullbackFunctor w (𝟙 (Spec B)) I).obj F
  let G' := (coherentPullback a).obj G
  let β' := formalModificationBaseChangeIso a b p w h.w (𝟙 (Spec B)) I F G β
  let α' := formalModificationComparisonBaseChange a b p w h (𝟙 (Spec B)) I F G α
  let : IsAdicComplete I (AdicCompletion I B) :=
    AdicCompletion.isAdicComplete (M := B) (IsNoetherian.noetherian I)
  let : IsAdicComplete (Ideal.map φ.hom I) S :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I B)).mpr inferInstance
  let : IsAdicComplete
      (affineIdeal S (idealThickeningIdealSheaf (w ≫ 𝟙 (Spec B)) I)) S := by
    dsimp only [w]
    rw [Category.comp_id, idealThickeningIdealSheaf_specMap,
      affineIdeal_idealThickeningIdealSheaf]
    infer_instance
  let : IsIso (b ∣_ (w ⁻¹ᵁ U)) := Scheme.Hom.isIso_restrict_pullback p w U
  have hU' : ((w ⁻¹ᵁ U : (Spec S).Opens) : Set (Spec S))ᶜ ⊆ (K.comap w).support := by
    intro x hx
    rw [IdealSheafData.support_comap]
    exact hU hx
  have hα' := formalModificationComparisonBaseChange_diagram a b p w h
    (𝟙 (Spec B)) I F G β α (affineModificationComparison_original_diagram p I F G β.hom)
  obtain ⟨t, ht, hb⟩ := affineModificationComparison_overBase_hasBoundedDefects b G'
    (w ≫ 𝟙 (Spec B)) I F' β' α' hα' (K.comap w) (w ⁻¹ᵁ U) hU'
  let : G.obj.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (G.property R j).1)
  have hm : IsIso ((cartesianBaseChangeMap a b p w h).app G.obj) := by
    rw [← moduleBaseChangeMap_eq_cartesianBaseChangeMap]
    exact moduleBaseChangeMap_completion_isIso I p G.obj
  let c : (coherentPullback w).obj (properPushforwardCoefficient p G) ≅
      properPushforwardCoefficient b G' :=
    ObjectProperty.isoMk _
      (@asIso (Spec S).Modules _ _ _ ((cartesianBaseChangeMap a b p w h).app G.obj) hm)
  have hp := defectsKilled_of_originalComposite
    ((baseIdealPullbackFunctor w (𝟙 (Spec B)) I).map α)
    (baseIdealPullbackCompletionIso w (𝟙 (Spec B)) I (properPushforwardCoefficient p G))
    ((completionFunctor (Spec S) (idealThickeningIdealSheaf (w ≫ 𝟙 (Spec B)) I)).mapIso c)
    ((completionFunctor (Spec S) (idealThickeningIdealSheaf (w ≫ 𝟙 (Spec B)) I)).map
      (properPushforwardBaseChangeCoefficient a b p w h G))
    rfl α' (formalModificationComparisonBaseChange_eq a b p w h
      (𝟙 (Spec B)) I F G α) hb
  exact ⟨t, ht, completionPullback_formal_defects_reflect I α K t hp⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
