/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Coherence
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalReflection
public import Aglib.CategoryTheory.Functor.CompositionCubeWhole

/-! # Original constant-ring underlying composition and mate reflection

The given site-composition isomorphism constructs the original ringed and
abelian image comparisons. Their actual section maps prove direct-image
compatibility, which is reflected through the original adjunction mates to
inverse-image compatibility. Equality transport preserves these same selected
comparisons, and the existing whole composition-cube factory applies unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf.ConstantRing

universe u₁ v₁ u₂ v₂ u₃ v₃ r w

section SingleImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K]
  [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]

/-- The original direct-image underlying object is unchanged. -/
theorem moduleDirectImage_underlying_obj (M : ModuleSheaf.{u₂, v₂, r, w} K Λ) :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj
        ((moduleDirectImage F J K Λ).obj M) =
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj
        ((SheafOfModules.toSheaf.{w} (constantRing K Λ)).obj M) := rfl

/-- The original direct image retains the underlying morphism. -/
theorem moduleDirectImage_underlying_map {M N : ModuleSheaf.{u₂, v₂, r, w} K Λ}
    (a : M ⟶ N) :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).map
        ((moduleDirectImage F J K Λ).map a) =
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((SheafOfModules.toSheaf.{w} (constantRing K Λ)).map a) := rfl

end SingleImage

section Composition

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (Λ : Type r) [Ring Λ] [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]

variable [HasWeakSheafify J RingCat.{r}] [HasWeakSheafify K RingCat.{r}]
  [HasWeakSheafify L RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [K.WEqualsLocallyBijective RingCat.{r}]
  [L.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify L AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [L.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [L.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The inverse module composition has the exact original abelian site comparison underneath. -/
theorem moduleDirectImageCompIso_inv_underlying (e : F ⋙ G ≅ H)
    (M : ModuleSheaf.{u₃, v₃, r, w} L Λ) :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).map
        ((moduleDirectImageCompIso F G H J K L Λ e).inv.app M) =
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).hom.app
        ((SheafOfModules.toSheaf.{w} (constantRing L Λ)).obj M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact moduleDirectImageCompIso_inv_app_apply F G H J K L Λ e M U x

/-- The forward original module composition has the inverse abelian comparison underneath. -/
theorem moduleDirectImageCompIso_hom_underlying (e : F ⋙ G ≅ H)
    (M : ModuleSheaf.{u₃, v₃, r, w} L Λ) :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).map
        ((moduleDirectImageCompIso F G H J K L Λ e).hom.app M) =
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).inv.app
        ((SheafOfModules.toSheaf.{w} (constantRing L Λ)).obj M) := by
  have h : ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).mapIso
      ((moduleDirectImageCompIso F G H J K L Λ e).app M)).symm =
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).app
        ((SheafOfModules.toSheaf.{w} (constantRing L Λ)).obj M) := by
    apply Iso.ext
    exact moduleDirectImageCompIso_inv_underlying F G H J K L Λ e M
  exact congrArg Iso.inv h

/-- The three original underlying direct-image comparisons obey the original composition law. -/
theorem moduleDirectImageUnderlyingIso_comp (e : F ⋙ G ≅ H)
    (M : ModuleSheaf.{u₃, v₃, r, w} L Λ) :
    (SheafOfModules.toSheaf.{w} (constantRing J Λ)).map
        ((moduleDirectImageCompIso F G H J K L Λ e).hom.app M) ≫
      (moduleDirectImageUnderlyingIso F J K Λ).hom.app
        ((moduleDirectImage G K L Λ).obj M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((moduleDirectImageUnderlyingIso G K L Λ).hom.app M) =
    (moduleDirectImageUnderlyingIso H J L Λ).hom.app M ≫
      (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).inv.app
        ((SheafOfModules.toSheaf.{w} (constantRing L Λ)).obj M) := by
  let a := (SheafOfModules.toSheaf.{w} (constantRing J Λ)).map
    ((moduleDirectImageCompIso F G H J K L Λ e).hom.app M)
  let b := (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).inv.app
    ((SheafOfModules.toSheaf.{w} (constantRing L Λ)).obj M)
  let Z := (moduleDirectImage G K L Λ ⋙
    SheafOfModules.toSheaf.{w} (constantRing K Λ)).obj M
  let P := F.sheafPushforwardContinuous AddCommGrpCat.{w} J K
  change a ≫ 𝟙 (P.obj Z) ≫ P.map (𝟙 Z) = 𝟙 _ ≫ b
  exact (congrArg (fun z => a ≫ 𝟙 (P.obj Z) ≫ z) (P.map_id Z)).trans
    ((congrArg (fun z => a ≫ z) (Category.id_comp (𝟙 (P.obj Z)))).trans
      ((Category.comp_id a).trans
        ((moduleDirectImageCompIso_hom_underlying F G H J K L Λ e M).trans
          (Category.id_comp b).symm)))

variable [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, F.op.HasLeftKanExtension P]
  [∀ P : Dᵒᵖ ⥤ ModuleCat.{w} Λ, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} Λ, H.op.HasLeftKanExtension P]
  [HasWeakSheafify K (ModuleCat.{w} Λ)] [HasWeakSheafify L (ModuleCat.{w} Λ)]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
  [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{w}, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, H.op.HasLeftKanExtension P]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions G.op]
  [(forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).PreservesLeftKanExtensions H.op]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [L.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Reflect the original direct-image equation through the actual mates, before geometry. -/
theorem moduleInverseImageUnderlyingIso_inv_comp (e : F ⋙ G ≅ H)
    (c : H.sheafPullback AddCommGrpCat.{w} J L ≅
      F.sheafPullback AddCommGrpCat.{w} J K ⋙ G.sheafPullback AddCommGrpCat.{w} K L)
    (hc : conjugateEquiv
      ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).comp
        (G.sheafAdjunctionContinuous AddCommGrpCat.{w} K L))
      (H.sheafAdjunctionContinuous AddCommGrpCat.{w} J L) c.hom =
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).hom)
    (M : ModuleSheaf.{u₁, v₁, r, w} J Λ) :
    c.hom.app
        ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M) ≫
      (G.sheafPullback AddCommGrpCat.{w} K L).map
        ((moduleInverseImageUnderlyingIso F J K Λ).inv.app M) ≫
      (moduleInverseImageUnderlyingIso G K L Λ).inv.app
        ((moduleInverseImage F J K Λ).obj M) =
    (moduleInverseImageUnderlyingIso H J L Λ).inv.app M ≫
      (SheafOfModules.toSheaf.{w} (constantRing L Λ)).map
        ((moduleInverseImageCompIso F G H J K L Λ e).hom.app M) := by
  apply verticalSquareEquation
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso F J K Λ).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso G K L Λ).inv)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso H J L Λ).inv)
    (moduleInverseImageCompIso F G H J K L Λ e)
    c
    (moduleDirectImageCompIso F G H J K L Λ e)
    (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{w} J K L).symm
    (moduleInverseImageAdjunction F J K Λ)
    (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
    (moduleInverseImageAdjunction G K L Λ)
    (G.sheafAdjunctionContinuous AddCommGrpCat.{w} K L)
    (moduleInverseImageAdjunction H J L Λ)
    (H.sheafAdjunctionContinuous AddCommGrpCat.{w} J L)
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      (moduleInverseImageAdjunction H J L Λ)
      ((moduleInverseImageAdjunction F J K Λ).comp (moduleInverseImageAdjunction G K L Λ))
      (moduleDirectImageCompIso F G H J K L Λ e))
    hc _ M
  intro N
  change _ ≫ ((mateEquiv (moduleInverseImageAdjunction F J K Λ)
      (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso F J K Λ).inv)).natTrans).app _ ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        (((mateEquiv (moduleInverseImageAdjunction G K L Λ)
      (G.sheafAdjunctionContinuous AddCommGrpCat.{w} K L)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso G K L Λ).inv)).natTrans).app N) =
    ((mateEquiv (moduleInverseImageAdjunction H J L Λ)
      (H.sheafAdjunctionContinuous AddCommGrpCat.{w} J L)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso H J L Λ).inv)).natTrans).app N ≫ _
  rw [mate_moduleInverseImageUnderlyingIso_inv, mate_moduleInverseImageUnderlyingIso_inv,
    mate_moduleInverseImageUnderlyingIso_inv]
  exact moduleDirectImageUnderlyingIso_comp F G H J K L Λ e N

end Composition

end ModuleCat.Sheaf.ConstantRing

namespace CategoryTheory.Functor

/-- Literal index equality transports the original comparison, with no new chosen isomorphism. -/
theorem comparisonTransportEquation_eqToIso {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    {I : Sort*} (F : I → A ⥤ B) (G : I → A' ⥤ B')
    (U : A ⥤ A') (V : B ⥤ B') (e : ∀ i, F i ⋙ V ≅ U ⋙ G i)
    {i j : I} (h : i = j) :
    ComparisonTransportEquation (e i) (e j)
      (eqToIso (congrArg F h)) (eqToIso (congrArg G h)) := by
  subst j
  intro M
  simp

end CategoryTheory.Functor
