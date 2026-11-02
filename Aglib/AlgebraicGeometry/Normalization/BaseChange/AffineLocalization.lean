/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Relative normalization and affine localization

The comparison is the original `Scheme.Hom.normalizationPullback`, including
its structural and original-source projection equations. The proof follows
the affine calculation of Mathlib's smooth comparison, using the proved
localization comparison of integral closures instead of smoothness.

Additional contributions: Copyright (c) 2026 kangxyz. All rights reserved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Relative normalization commutes with an actual affine localization.
The localization algebra structure is induced by the original section map.
Flatness is retained explicitly for the canonical section pushout comparisons. -/
theorem normalizationPullback_isIso_of_affineLocalization
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S] [IsAffine Y] [Flat g]
    (M : Submonoid Γ(S, ⊤))
    (hM : letI := (g.appLE ⊤ ⊤ (by simp)).hom.toAlgebra;
      IsLocalization M Γ(Y, ⊤)) : IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  let U : S.Opens := ⊤
  let V : Y.Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top S
  have hV : IsAffineOpen V := isAffineOpen_top Y
  have hxV : (pullback.snd f.fromNormalization g) x ∈ V := trivial
  have hVU : V ≤ g ⁻¹ᵁ U := by simp [U, V]
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  let : IsLocalization M Γ(Y, V) := hM
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

end AlgebraicGeometry.Scheme.Hom
