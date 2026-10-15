/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.SheafificationPushforward
public import Aglib.Algebra.Category.ModuleCat.Presheaf.TensorPushforward

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorPushforward.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 121]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensor and module-sheaf pushforward

Combine the actual presheaf tensor comparison with the original sheafification comparison.
The result preserves both-variable naturality and the literal sheafification-unit square.
The ring-sheaf morphism is required to be invertible on the underlying presheaf.
-/

@[expose] public section
noncomputable section
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
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
/-- The original pushforward, forgetting only commutativity of the ring sheaf. -/
abbrev modulePushforward : SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing S :=
  SheafOfModules.pushforward
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩
/-- Tensor commutes with the original pushforward along an invertible section-ring map. -/
def tensorPushforwardIso [IsIso φ.hom] (M N : SheafOfModulesOfCommRing R) :
    (tensorLeftFunctor S ((modulePushforward φ).obj M)).obj ((modulePushforward φ).obj N) ≅
      (modulePushforward φ).obj ((tensorLeftFunctor R M).obj N) :=
  (associatedSheaf S).mapIso
    (PresheafOfModulesOfCommRing.pushforwardTensorIso φ.hom
      ((toPresheaf R).obj M) ((toPresheaf R).obj N)) ≪≫
  (SheafOfModules.sheafificationPushforwardIso
    (F := F) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ⟨whiskerRight φ.hom (forget₂ CommRingCat RingCat)⟩).app
    (show PresheafOfModulesOfCommRing.{u} R.obj from
      ((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))
/-- Naturality in both original module-sheaf variables. -/
theorem tensorPushforwardIso_naturality [IsIso φ.hom]
    {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    (associatedSheaf S).map
        (((toPresheaf S).map ((modulePushforward φ).map f)) ⊗ₘ
          ((toPresheaf S).map ((modulePushforward φ).map g))) ≫
        (tensorPushforwardIso φ M' N').hom =
      (tensorPushforwardIso φ M N).hom ≫
        (modulePushforward φ).map ((associatedSheaf R).map
          (((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))) := by
  dsimp only [tensorPushforwardIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  have h := PresheafOfModulesOfCommRing.pushforwardTensorHom_naturality φ.hom
    ((toPresheaf R).map f) ((toPresheaf R).map g)
  change (((toPresheaf S).map ((modulePushforward φ).map f)) ⊗ₘ
    ((toPresheaf S).map ((modulePushforward φ).map g))) ≫
      (PresheafOfModulesOfCommRing.pushforwardTensorIso φ.hom
        ((toPresheaf R).obj M') ((toPresheaf R).obj N')).hom = _ at h
  rw [h]
  simp only [Functor.map_comp, Category.assoc,
    PresheafOfModulesOfCommRing.pushforwardTensorIso_hom]
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
/-- The literal unit of module sheafification, viewed on commutative-ring modules. -/
def associatedSheafUnit (T : Sheaf J CommRingCat.{u}) :
    𝟭 (PresheafOfModulesOfCommRing.{u} T.obj) ⟶ associatedSheaf T ⋙ toPresheaf T :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj T) (𝟙 _)).unit
/-- The tensor comparison carries the original sheafification unit
to the restriction of the original unit. -/
theorem tensorPushforwardIso_unit [IsIso φ.hom] (M N : SheafOfModulesOfCommRing R) :
    (associatedSheafUnit S).app
        (((toPresheaf S).obj ((modulePushforward φ).obj M)) ⊗
          ((toPresheaf S).obj ((modulePushforward φ).obj N))) ≫
      (toPresheaf S).map (tensorPushforwardIso φ M N).hom =
    PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
        ((toPresheaf R).obj M) ((toPresheaf R).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward φ.hom).map
        ((associatedSheafUnit R).app
          (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))) := by
  let μ := PresheafOfModulesOfCommRing.pushforwardTensorHom φ.hom
    ((toPresheaf R).obj M) ((toPresheaf R).obj N)
  have h := (associatedSheafUnit S).naturality μ
  dsimp only [tensorPushforwardIso, Iso.trans_hom, Functor.mapIso_hom]
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
