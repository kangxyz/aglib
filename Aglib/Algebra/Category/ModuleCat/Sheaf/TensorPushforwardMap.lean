/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorPushforwardMap.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 254]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The tensor map for module-sheaf pushforward

Construct the original tensor pushforward map for a continuous ringed-site map.
Prove both-variable naturality, its sheafification-unit equation and its left-unit
compatibility. No cocontinuity or invertibility of the ring map is assumed.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
namespace SheafOfModulesOfCommRing
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
/-- The actual tensor pushforward arrow, without invertibility hypotheses. -/
def pushforwardTensorMap (M N : SheafOfModulesOfCommRing R) :
    (tensorLeftFunctor S ((modulePushforward φ).obj M)).obj ((modulePushforward φ).obj N) ⟶
      (modulePushforward φ).obj ((tensorLeftFunctor R M).obj N) :=
  (associatedSheaf S).map
    (PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
      ((toPresheaf R).obj M) ((toPresheaf R).obj N)) ≫
  (SheafOfModules.sheafificationPushforwardComparison
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩).app
      (show PresheafOfModulesOfCommRing.{u} R.obj from
        ((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))
/-- On the invertible cocontinuous locus this is the previously constructed original comparison. -/
theorem pushforwardTensorMap_eq_iso_hom [F.IsCocontinuous J K] [IsIso φ.hom]
    (M N : SheafOfModulesOfCommRing R) :
    pushforwardTensorMap φ M N = (tensorPushforwardIso φ M N).hom := rfl
/-- Naturality in both original module-sheaf variables. -/
theorem pushforwardTensorMap_naturality
    {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    (associatedSheaf S).map
        (((toPresheaf S).map ((modulePushforward φ).map f)) ⊗ₘ
          ((toPresheaf S).map ((modulePushforward φ).map g))) ≫
        pushforwardTensorMap φ M' N' =
      pushforwardTensorMap φ M N ≫
        (modulePushforward φ).map ((associatedSheaf R).map
          (((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))) := by
  dsimp only [pushforwardTensorMap]
  rw [← Category.assoc, ← Functor.map_comp]
  have h := PresheafOfModulesOfCommRing.pushforwardTensorHom_naturality φ.hom
    ((toPresheaf R).map f) ((toPresheaf R).map g)
  change (((toPresheaf S).map ((modulePushforward φ).map f)) ⊗ₘ
    ((toPresheaf S).map ((modulePushforward φ).map g))) ≫
      (PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
        ((toPresheaf R).obj M') ((toPresheaf R).obj N')) = _ at h
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  apply congrArg (fun q => (associatedSheaf S).map
    (PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
      ((toPresheaf R).obj M) ((toPresheaf R).obj N)) ≫ q)
  exact (SheafOfModules.sheafificationPushforwardComparison
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩).naturality
      (show ((toPresheaf R).obj M ⊗ (toPresheaf R).obj N) ⟶
        ((toPresheaf R).obj M' ⊗ (toPresheaf R).obj N') from
          ((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))
/-- The tensor comparison carries the original sheafification unit
to the restriction of the original unit. -/
theorem pushforwardTensorMap_unit (M N : SheafOfModulesOfCommRing R) :
    (associatedSheafUnit S).app
        (((toPresheaf S).obj ((modulePushforward φ).obj M)) ⊗
          ((toPresheaf S).obj ((modulePushforward φ).obj N))) ≫
      (toPresheaf S).map (pushforwardTensorMap φ M N) =
    PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
        ((toPresheaf R).obj M) ((toPresheaf R).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward φ.hom).map
        ((associatedSheafUnit R).app
          (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))) := by
  let μ := PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
    ((toPresheaf R).obj M) ((toPresheaf R).obj N)
  have h := (associatedSheafUnit S).naturality μ
  dsimp only [pushforwardTensorMap]
  rw [Functor.map_comp, ← Category.assoc]
  change (_ ≫ (toPresheaf S).map ((associatedSheaf S).map μ)) ≫ _ = _
  dsimp only [Functor.id_map, Functor.comp_map] at h
  erw [← h, Category.assoc]
  congr 1
  exact SheafOfModules.sheafificationPushforwardComparison_unit
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩
    (show PresheafOfModulesOfCommRing.{u} R.obj from
      ((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))
end SheafOfModulesOfCommRing
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
namespace SheafOfModulesOfCommRing
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
/-- The original unit comparison sends a sheafification generator to the presheaf unitor. -/
theorem associatedSheafUnit_tensorLeftUnitIso (T : Sheaf J CommRingCat.{u})
    (N : SheafOfModulesOfCommRing T) :
    (associatedSheafUnit T).app
        (𝟙_ (PresheafOfModulesOfCommRing.{u} T.obj) ⊗ ((toPresheaf T).obj N)) ≫
      (toPresheaf T).map ((tensorLeftUnitIso T).hom.app N) =
        (λ_ ((toPresheaf T).obj N)).hom := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj T)
      (𝟙 _)).unit_comp_map_eq_iff _ _ |>.mpr
  exact tensorLeftUnitIso_hom_app T N
/-- The original structure-module arrow used in the pushforward tensor unit law. -/
abbrev tensorPushforwardUnitMap :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⟶
      (modulePushforward φ).obj
        (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :=
  SheafOfModules.unitToPushforwardObjUnit
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩
omit [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The pointwise tensor and structure-module maps retain the original left unitor. -/
theorem presheaf_pushforwardTensorMap_leftUnit (N : SheafOfModulesOfCommRing R) :
    (((toPresheaf S).map (tensorPushforwardUnitMap φ)) ⊗ₘ
        𝟙 ((toPresheaf S).obj ((modulePushforward φ).obj N))) ≫
      PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
        (𝟙_ (PresheafOfModulesOfCommRing.{u} R.obj)) ((toPresheaf R).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward φ.hom).map
        (λ_ ((toPresheaf R).obj N)).hom =
      (λ_ ((toPresheaf S).obj ((modulePushforward φ).obj N))).hom := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r n
  change (λ_ (((toPresheaf R).obj N).obj (F.op.obj U))).hom
    (CategoryTheory.Functor.LaxMonoidal.μ
      (ModuleCat.restrictScalars (φ.hom.app U).hom)
      (𝟙_ (ModuleCat.{u} (R.obj.obj (F.op.obj U))))
      (((toPresheaf R).obj N).obj (F.op.obj U))
      (((φ.hom.app U).hom r) ⊗ₜ[S.obj.obj U] n)) = _
  rw [ModuleCat.restrictScalars_μ_tmul]
  rfl
/-- The original pushforward tensor arrow respects the actual unit comparison. -/
theorem pushforwardTensorMap_leftUnit (N : SheafOfModulesOfCommRing R) :
    ((tensorFunctor S).map (tensorPushforwardUnitMap φ)).app
        ((modulePushforward φ).obj N) ≫
      pushforwardTensorMap φ
        (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) N ≫
      (modulePushforward φ).map ((tensorLeftUnitIso R).hom.app N) =
        (tensorLeftUnitIso S).hom.app ((modulePushforward φ).obj N) := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
      (𝟙 _)).homEquiv _ _ |>.injective
  change (associatedSheafUnit S).app _ ≫ (toPresheaf S).map _ =
    (associatedSheafUnit S).app _ ≫ (toPresheaf S).map _
  trans (λ_ ((toPresheaf S).obj ((modulePushforward φ).obj N))).hom
  · simp only [Functor.map_comp, tensorFunctor_map_app]
    let q := ((toPresheaf S).map (tensorPushforwardUnitMap φ)) ⊗ₘ
      𝟙 ((toPresheaf S).obj ((modulePushforward φ).obj N))
    have hq := (associatedSheafUnit S).naturality q
    dsimp only [Functor.id_map, Functor.comp_map] at hq
    rw [← Category.assoc]
    erw [← hq, Category.assoc]
    rw [← Category.assoc _ _
      ((toPresheaf S).map ((modulePushforward φ).map ((tensorLeftUnitIso R).hom.app N)))]
    erw [pushforwardTensorMap_unit φ
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) N]
    rw [Category.assoc]
    have hl := congrArg (fun a => (PresheafOfModulesOfCommRing.pushforward φ.hom).map a)
      (associatedSheafUnit_tensorLeftUnitIso R N)
    rw [Functor.map_comp] at hl
    change (PresheafOfModulesOfCommRing.pushforward φ.hom).map
      ((associatedSheafUnit R).app
        (𝟙_ (PresheafOfModulesOfCommRing.{u} R.obj) ⊗ ((toPresheaf R).obj N))) ≫
        (toPresheaf S).map ((modulePushforward φ).map ((tensorLeftUnitIso R).hom.app N)) =
      (PresheafOfModulesOfCommRing.pushforward φ.hom).map
        (λ_ ((toPresheaf R).obj N)).hom at hl
    erw [hl]
    exact presheaf_pushforwardTensorMap_leftUnit φ N
  · exact (associatedSheafUnit_tensorLeftUnitIso S ((modulePushforward φ).obj N)).symm
end SheafOfModulesOfCommRing
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
namespace SheafOfModulesOfCommRing
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
/-- The original tensor pushforward sends a sheafification generator to the same source tensor. -/
theorem pushforwardTensorMap_tensorSection (M N : SheafOfModulesOfCommRing R)
    (U : Cᵒᵖ) (m : ((toPresheaf S).obj ((modulePushforward φ).obj M)).obj U)
    (n : ((toPresheaf S).obj ((modulePushforward φ).obj N)).obj U) :
    (pushforwardTensorMap φ M N).val.app U
        (tensorSection S ((modulePushforward φ).obj M) ((modulePushforward φ).obj N) U m n) =
      tensorSection R M N (F.op.obj U) m n := by
  have h := congrArg (fun a => a.app U (m ⊗ₜ[S.obj.obj U] n))
    (pushforwardTensorMap_unit φ M N)
  change (pushforwardTensorMap φ M N).val.app U
    (tensorSection S ((modulePushforward φ).obj M) ((modulePushforward φ).obj N) U m n) =
    ((associatedSheafUnit R).app
      (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))).app (F.op.obj U)
      (CategoryTheory.Functor.LaxMonoidal.μ
        (ModuleCat.restrictScalars (φ.hom.app U).hom)
        (((toPresheaf R).obj M).obj (F.op.obj U))
        (((toPresheaf R).obj N).obj (F.op.obj U)) (m ⊗ₜ[S.obj.obj U] n)) at h
  rw [ModuleCat.restrictScalars_μ_tmul] at h
  exact h
end SheafOfModulesOfCommRing
end
