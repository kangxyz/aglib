/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageSiteSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # The ordinary étale chart isomorphism is the original exchange mate -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

private theorem continuous_three_transforms
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {P₀ P₁ P₂ P₃ : C ⥤ D}
    [P₀.IsContinuous J K] [P₁.IsContinuous J K]
    [P₂.IsContinuous J K] [P₃.IsContinuous J K]
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) :
    Functor.sheafPushforwardContinuousNatTrans c A J K ≫
      Functor.sheafPushforwardContinuousNatTrans b A J K ≫
        Functor.sheafPushforwardContinuousNatTrans a A J K =
    Functor.sheafPushforwardContinuousNatTrans (a ≫ b ≫ c) A J K := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (c.app U.unop).op ≫ F.obj.map (b.app U.unop).op ≫
    F.obj.map (a.app U.unop).op = F.obj.map (a.app U.unop ≫
      b.app U.unop ≫ c.app U.unop).op
  simp only [op_comp, Functor.map_comp, Category.assoc]

private theorem iso_chain_hom_of_eq {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ : C} (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (r : X₂ ⟶ X₃)
    (hp : a.hom = p) (hq : b.hom = q) (hr : c.hom = r) :
    (a ≪≫ b ≪≫ c).hom = p ≫ q ≫ r := by
  simp only [Iso.trans_hom, hp, hq, hr]

private theorem transported_exchange_unit
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (G : A ⥤ B) (H : D ⥤ C) (R : C ⥤ B) (N : D ⥤ A)
    {D₀ D₁ : D} (d : D₀ ≅ D₁) {B₀ : B} {C₀ C₁ : C}
    (η : B₀ ⟶ R.obj C₀) (e : C₀ ⟶ C₁) (E : C₁ ⟶ H.obj D₁)
    (θ : B₀ ⟶ G.obj (N.obj D₀))
    (ρ₀ : G.obj (N.obj D₀) ⟶ R.obj (H.obj D₀))
    (ρ₁ : G.obj (N.obj D₁) ⟶ R.obj (H.obj D₁))
    (hn : G.map (N.map d.hom) ≫ ρ₁ = ρ₀ ≫ R.map (H.map d.hom))
    (hg : η ≫ R.map e ≫ R.map E = θ ≫ G.map (N.map d.hom) ≫ ρ₁)
    (b : C₀ ⟶ H.obj D₀) (hb : b = e ≫ E ≫ H.map d.inv) :
    θ ≫ ρ₀ = η ≫ R.map b := by
  rw [hn] at hg
  have hc := congrArg (fun k => k ≫ R.map (H.map d.inv)) hg
  simp only [Category.assoc] at hc
  rw [← R.map_comp (H.map d.hom) (H.map d.inv), ← H.map_comp d.hom d.inv,
    d.hom_inv_id, H.map_id, R.map_id,
    Category.comp_id] at hc
  simpa only [hb, Functor.map_comp, Category.assoc] using hc.symm

private theorem adjunction_unit_ext {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D}
    (a b : L.obj X ⟶ Y)
    (h : adj.unit.app X ≫ R.map a = adj.unit.app X ≫ R.map b) : a = b :=
  (adj.homEquiv X Y).injective h

private theorem exchange_of_restriction
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (G : A ⥤ B) (H : D ⥤ C) {L₀ M₀ : A ⥤ D} {N : D ⥤ A}
    {L₁ M₁ : B ⥤ C} {R : C ⥤ B}
    (a₀ : L₀ ⊣ N) (a₁ : L₁ ⊣ R) (m₀ : M₀ ⊣ N) (m₁ : M₁ ⊣ R)
    (e₀ : L₀ ≅ M₀) (e₁ : L₁ ≅ M₁) (E : G ⋙ M₁ ≅ M₀ ⋙ H)
    (ρ : N ⋙ G ⟶ H ⋙ R) (β : G ⋙ L₁ ⟶ L₀ ⋙ H)
    (h₀ : ∀ F, a₀.unit.app F ≫ N.map (e₀.hom.app F) = m₀.unit.app F)
    (h₁ : ∀ F, a₁.unit.app F ≫ R.map (e₁.hom.app F) = m₁.unit.app F)
    (hE : ∀ F, m₁.unit.app (G.obj F) ≫ R.map (E.hom.app F) =
      G.map (m₀.unit.app F) ≫ ρ.app (M₀.obj F))
    (hβ : ∀ F, G.map (a₀.unit.app F) ≫ ρ.app (L₀.obj F) =
      a₁.unit.app (G.obj F) ≫ R.map (β.app F)) :
    (Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫ Functor.isoWhiskerRight e₀.symm H).hom = β := by
  apply NatTrans.ext
  funext F
  have hg := hE F
  rw [← h₁, ← h₀] at hg
  simp only [Category.assoc, Functor.map_comp] at hg
  have hu := transported_exchange_unit G H R N (e₀.app F)
    (a₁.unit.app (G.obj F)) (e₁.hom.app (G.obj F)) (E.hom.app F)
    (G.map (a₀.unit.app F)) (ρ.app (L₀.obj F)) (ρ.app (M₀.obj F))
    (ρ.naturality (e₀.hom.app F)) hg
    ((Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫
      Functor.isoWhiskerRight e₀.symm H).hom.app F) rfl
  exact adjunction_unit_ext a₁ _ _ (hu.symm.trans (hβ F))

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

local instance {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    (siteBaseChange f ⋙ siteBaseChange g).IsContinuous
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T) :=
  Functor.isContinuous_comp (siteBaseChange f) (siteBaseChange g)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T)

private theorem directImageCompIso_hom_transform {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).hom =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).hom
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.id_comp _

private theorem directImageCompIso_inv_transform {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    (directImageCompIso f g).inv =
      Functor.sheafPushforwardContinuousNatTrans (siteBaseChangeComp f g).inv
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology T) := by
  exact Category.comp_id _

private theorem directImage_eqToIso_transform {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) :
    (eqToIso (congrArg (fun k => directImage k) h)).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (eqToHom (congrArg (fun k => siteBaseChange k) h.symm))
        AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
        (Scheme.smallEtaleTopology S) := by
  subst g
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (𝟙 _) = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

private theorem directImageSquareIso_transform {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    (directImageSquareIso f f' g g' h).hom =
      Functor.sheafPushforwardContinuousNatTrans
        (siteBaseChangeSquareIso f f' g g' h).hom AddCommGrpCat.{u + 1}
        (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X') := by
  refine (iso_chain_hom_of_eq (directImageCompIso f g')
    (eqToIso (congrArg (fun k => directImage k) h.symm))
    (directImageCompIso g f').symm _ _ _
    (directImageCompIso_hom_transform f g') (directImage_eqToIso_transform h.symm)
    (directImageCompIso_inv_transform g f')).trans ?_
  exact continuous_three_transforms (A := AddCommGrpCat.{u + 1})
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X')
    (siteBaseChangeComp g f').inv
    (eqToHom (congrArg (fun k => siteBaseChange k) h)) (siteBaseChangeComp f g').hom

private theorem directImageSquareIso_app_hom {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (F : AbelianSheaf.{u, u + 1} X') (U : S.Etale) :
    ((directImageSquareIso f f' g g' h).hom.app F).hom.app (op U) =
      F.obj.map ((siteBaseChangeSquareIso f f' g g' h).hom.app U).op :=
  congrArg (fun a => (a.app F).hom.app (op U))
    (directImageSquareIso_transform f f' g g' h)

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]

/-- The genuine restriction comparison, transported by the original inverse-image isomorphisms. -/
def etaleBaseChangeIso :
    directImage f ⋙ inverseImage g ≅
      inverseImage (pullback.snd g f) ⋙ directImage (pullback.fst g f) :=
  Functor.isoWhiskerLeft (directImage f) (inverseImageEtaleIso g) ≪≫
    etaleDirectImageRestrictionIso f g ≪≫
      Functor.isoWhiskerRight (inverseImageEtaleIso (pullback.snd g f)).symm
        (directImage (pullback.fst g f))

private theorem etaleRestriction_directImage_unit (F : AbelianSheaf.{u, u + 1} X) :
    (((siteEtalePostcomposeAdj g).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S)).unit.app ((directImage f).obj F)) ≫
        (directImage g).map ((etaleDirectImageRestrictionIso f g).hom.app F) =
      (directImage f).map
        (((siteEtalePostcomposeAdj (pullback.snd g f)).sheafPushforwardContinuous
          (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology (pullback g f))
          (Scheme.smallEtaleTopology X)).unit.app F) ≫
        (directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app ((etaleRestriction (pullback.snd g f)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map ((siteBaseChange f).map ((siteEtalePostcomposeAdj g).counit.app U.unop)).op ≫
      F.obj.map ((siteEtaleDirectImageRestrictionIso f g).hom.app
        ((siteBaseChange g).obj U.unop)).op =
    F.obj.map ((siteEtalePostcomposeAdj (pullback.snd g f)).counit.app
      ((siteBaseChange f).obj U.unop)).op ≫
        ((directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app ((etaleRestriction (pullback.snd g f)).obj F)).hom.app U
  rw [directImageSquareIso_app_hom]
  change _ = F.obj.map
    ((siteEtalePostcomposeAdj (pullback.snd g f)).counit.app
      ((siteBaseChange f).obj U.unop)).op ≫
    F.obj.map ((siteEtalePostcompose (pullback.snd g f)).map
      ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).hom.app U.unop)).op
  exact ((F.obj.map_comp _ _).symm).trans
    ((congrArg (fun a => F.obj.map a.op)
      (siteEtaleDirectImageRestriction_counit f g U.unop).symm).trans
      (F.obj.map_comp _ _))

/-- The ordinary étale chart isomorphism is exactly the original underived exchange. -/
theorem etaleBaseChangeIso_hom :
    (etaleBaseChangeIso f g).hom =
      baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition := by
  exact exchange_of_restriction (directImage f) (directImage (pullback.fst g f))
    (inverseImageAdjunction (pullback.snd g f)) (inverseImageAdjunction g)
    ((siteEtalePostcomposeAdj (pullback.snd g f)).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology (pullback g f))
      (Scheme.smallEtaleTopology X))
    ((siteEtalePostcomposeAdj g).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S))
    (inverseImageEtaleIso (pullback.snd g f)) (inverseImageEtaleIso g)
    (etaleDirectImageRestrictionIso f g)
    (directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom
    (baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition)
    (inverseImageEtaleIso_unit (pullback.snd g f)) (inverseImageEtaleIso_unit g)
    (etaleRestriction_directImage_unit f g)
    (baseChangeMap_horizontal_unit f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition)

/-- Ordinary base change along an étale chart is an isomorphism for all abelian coefficients. -/
instance baseChangeMap_etale_isIso :
    IsIso (baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition) := by
  rw [← etaleBaseChangeIso_hom f g]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
