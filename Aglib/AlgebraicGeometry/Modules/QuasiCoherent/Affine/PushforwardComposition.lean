/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback

/-! # Whole right-adjoint coherence of original affine pushforwards

This is a conjugate consequence of the existing complete tilde theorem.
Its original section calculation remains the unique implementation there.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Original affine pushforward sections respect the actual raw scalar triangle.
This whole morphism equation requires no quasicoherence of the coefficient. -/
theorem pushforwardGlobalSectionsIso_ringHom_comp_inv
    {R S T : CommRingCat.{u}} (f : R →+* S) (g : S →+* T)
    (h : Spec.map (CommRingCat.ofHom (g.comp f) : R ⟶ T) =
      Spec.map (CommRingCat.ofHom g : S ⟶ T) ≫ Spec.map (CommRingCat.ofHom f : R ⟶ S))
    (G : (Spec T).Modules) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    (ModuleCat.restrictScalars f).map ((pushforwardGlobalSectionsIso ψ).inv.app G) ≫
      (pushforwardGlobalSectionsIso φ).inv.app ((pushforward (Spec.map ψ)).obj G) ≫
      moduleSpecΓFunctor.map ((pushforwardComp (Spec.map ψ) (Spec.map φ)).hom.app G) ≫
      moduleSpecΓFunctor.map ((pushforwardCongr h).inv.app G) =
        (ModuleCat.restrictScalarsComp f g).inv.app (moduleSpecΓFunctor.obj G) ≫
          (pushforwardGlobalSectionsIso χ).inv.app G := by
  intro φ ψ χ
  have hc := congrArg
    (conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f).comp
        ((ModuleCat.extendRestrictScalarsAdj g).comp (tilde.adjunction (R := T))))
      ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map χ))))
    (tildePullbackIso_ringHom_comp_hom_of_triangle f g h)
  rw [← conjugateEquiv_comp _
      ((tilde.adjunction (R := R)).comp ((pullbackPushforwardAdjunction (Spec.map φ)).comp
        (pullbackPushforwardAdjunction (Spec.map ψ)))),
    ← conjugateEquiv_comp _
      (((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map φ))).comp
        (pullbackPushforwardAdjunction (Spec.map ψ))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f).comp (tilde.adjunction (R := S))).comp
        (pullbackPushforwardAdjunction (Spec.map ψ))),
    ← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj f).comp
        ((tilde.adjunction (R := S)).comp (pullbackPushforwardAdjunction (Spec.map ψ))))] at hc
  rw [← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj (g.comp f)).comp (tilde.adjunction (R := T))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f).comp
        (ModuleCat.extendRestrictScalarsAdj g)).comp (tilde.adjunction (R := T)))] at hc
  rw [conjugateEquiv_whiskerLeft] at hc
  erw [conjugateEquiv_tildePullbackIso_hom ψ] at hc
  erw [conjugateEquiv_associator_hom (ModuleCat.extendRestrictScalarsAdj f)
    (tilde.adjunction (R := S)) (pullbackPushforwardAdjunction (Spec.map ψ))] at hc
  rw [conjugateEquiv_whiskerRight] at hc
  erw [conjugateEquiv_tildePullbackIso_hom φ] at hc
  rw [conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft, ← conjugateEquiv_comp _
      (pullbackPushforwardAdjunction (Spec.map ψ ≫ Spec.map φ)), conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_pullbackCongr_hom] at hc
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight] at hc
  erw [conjugateEquiv_tildePullbackIso_hom χ] at hc
  rw [show conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj f).comp
        (ModuleCat.extendRestrictScalarsAdj g)) (ModuleCat.extendRestrictScalarsAdj (g.comp f))
        (ModuleCat.extendScalarsComp f g).hom =
      (ModuleCat.restrictScalarsComp f g).inv from (conjugateEquiv _ _).apply_symm_apply _] at hc
  have hG := NatTrans.congr_app hc G
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp] using hG

end AlgebraicGeometry.Scheme.Modules
