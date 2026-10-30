/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Continuous.KanUnit
public import Mathlib.CategoryTheory.Sites.Pullback

/-! # The chosen pullback comparison with an actual left-Kan target sheaf

The actual alpha and its proved universal property construct the original
Lan comparison, chosen pullback comparison and sheafification comparison.
Their whole unit and adjunct laws determine the maps, including coefficient
naturality, without supplying the desired target Iso or unit equation.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe c₁ h₁ c₂ h₂ a b cE hE

variable {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
  {A : Type a} [Category.{b} A]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P] [HasWeakSheafify K A]

/-- The actual chosen Lan desc Iso, from alpha's original universal property. -/
def presheafLeftKanTargetIso (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
    (α : P ⟶ G.op ⋙ Q) [Q.IsLeftKanExtension α] : G.op.lan.obj P ≅ Q :=
  Functor.leftKanExtensionUnique _ (G.op.leftKanExtensionUnit P) _ α

/-- The whole original factorization by the actual chosen Kan unit. -/
theorem presheafLeftKanTargetIso_fac (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
    (α : P ⟶ G.op ⋙ Q) [Q.IsLeftKanExtension α] :
    G.op.leftKanExtensionUnit P ≫
      Functor.whiskerLeft G.op (presheafLeftKanTargetIso G P Q α).hom = α := by
  let : (G.op.lan.obj P).IsLeftKanExtension (G.op.leftKanExtensionUnit P) :=
    inferInstanceAs ((G.op.lan.obj P).IsLeftKanExtension (G.op.lanUnit.app P))
  change G.op.leftKanExtensionUnit P ≫ Functor.whiskerLeft G.op
    ((G.op.lan.obj P).descOfIsLeftKanExtension (G.op.leftKanExtensionUnit P)
      Q ((𝟙 P) ≫ α)) = α
  rw [Category.id_comp]
  exact Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- Naturality of the actual chosen Lan desc maps follows from the original alpha square. -/
theorem presheafLeftKanTargetIso_naturality
    {P P' : Cᵒᵖ ⥤ A} {Q Q' : Dᵒᵖ ⥤ A}
    (α : P ⟶ G.op ⋙ Q) (α' : P' ⟶ G.op ⋙ Q')
    [Q.IsLeftKanExtension α] [Q'.IsLeftKanExtension α']
    (p : P ⟶ P') (q : Q ⟶ Q')
    (hα : p ≫ α' = α ≫ Functor.whiskerLeft G.op q) :
    G.op.lan.map p ≫ (presheafLeftKanTargetIso G P' Q' α').hom =
      (presheafLeftKanTargetIso G P Q α).hom ≫ q := by
  apply Functor.hom_ext_of_isLeftKanExtension (G.op.lan.obj P) (G.op.lanUnit.app P)
  have hp : G.op.lanUnit.app P ≫ Functor.whiskerLeft G.op (G.op.lan.map p) =
      p ≫ G.op.lanUnit.app P' := (G.op.lanUnit.naturality p).symm
  have hP : G.op.lanUnit.app P ≫
      Functor.whiskerLeft G.op (presheafLeftKanTargetIso G P Q α).hom = α :=
    presheafLeftKanTargetIso_fac G P Q α
  have hP' : G.op.lanUnit.app P' ≫
      Functor.whiskerLeft G.op (presheafLeftKanTargetIso G P' Q' α').hom = α' :=
    presheafLeftKanTargetIso_fac G P' Q' α'
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [hp, hP, Category.assoc, hP']
  exact hα

/-- The same three original factors with the actual target sheaf. -/
def sheafPullbackTargetIso (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] :
    (G.sheafPullback A J K).obj P ≅ Q :=
  (sheafPullbackConstruction.sheafPullbackIso G A J K).app P ≪≫
    (presheafToSheaf K A).mapIso (presheafLeftKanTargetIso G P.obj Q.obj α) ≪≫
      (sheafificationIso Q).symm

/-- Its operational value is precisely the old chosen/Lan/sheafification chain. -/
theorem sheafPullbackTargetIso_eq_original (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] :
    sheafPullbackTargetIso G J K P Q α =
      (sheafPullbackConstruction.sheafPullbackIso G A J K).app P ≪≫
        (presheafToSheaf K A).mapIso (presheafLeftKanTargetIso G P.obj Q.obj α) ≪≫
          (sheafificationIso Q).symm := rfl

/-- The comparison has exactly the original alpha as the chosen unit map. -/
theorem sheafPullbackTargetIso_unit (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] :
    (G.sheafAdjunctionContinuous A J K).unit.app P ≫
      (G.sheafPushforwardContinuous A J K).map
        (sheafPullbackTargetIso G J K P Q α).hom = ⟨α⟩ := by
  let e := sheafPullbackConstruction.sheafPullbackIso G A J K
  let k := presheafLeftKanTargetIso G P.obj Q.obj α
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (G.sheafAdjunctionContinuous A J K)
    (sheafPullbackConstruction.sheafAdjunctionContinuous G A J K) P
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  let V := G.op.obj U
  have huU := congrArg (fun r => r.hom.app U) hu
  rw [sheafPullbackConstruction.unit_app_hom G A J K P] at huU
  change ((G.sheafAdjunctionContinuous A J K).unit.app P).hom.app U ≫
      (e.hom.app P).hom.app V =
    (G.op.leftKanExtensionUnit P.obj).app U ≫
      (toSheafify K (G.op.lan.obj P.obj)).app V at huU
  have hk : (G.op.leftKanExtensionUnit P.obj).app U ≫ k.hom.app V = α.app U :=
    NatTrans.congr_app (presheafLeftKanTargetIso_fac G P.obj Q.obj α) U
  have hn := (NatTrans.congr_app (toSheafify_naturality K k.hom) V).symm
  change (toSheafify K (G.op.lan.obj P.obj)).app V ≫
      ((presheafToSheaf K A).map k.hom).hom.app V =
    k.hom.app V ≫ (toSheafify K Q.obj).app V at hn
  have hr := congrArg (fun r => r.hom.app V) (sheafificationIso Q).hom_inv_id
  change (toSheafify K Q.obj).app V ≫ (sheafificationIso Q).inv.hom.app V = 𝟙 _ at hr
  let sourceUnit : P.obj.obj U ⟶ ((G.sheafPullback A J K).obj P).obj.obj V :=
    ((G.sheafAdjunctionContinuous A J K).unit.app P).hom.app U
  let chosenMap : ((G.sheafPullback A J K).obj P).obj.obj V ⟶
      ((presheafToSheaf K A).obj (G.op.lan.obj P.obj)).obj.obj V :=
    (e.hom.app P).hom.app V
  let kanUnit : P.obj.obj U ⟶ (G.op.lan.obj P.obj).obj V :=
    (G.op.leftKanExtensionUnit P.obj).app U
  let sheafUnit : (G.op.lan.obj P.obj).obj V ⟶
      ((presheafToSheaf K A).obj (G.op.lan.obj P.obj)).obj.obj V :=
    (toSheafify K (G.op.lan.obj P.obj)).app V
  let descMap : (G.op.lan.obj P.obj).obj V ⟶ Q.obj.obj V := k.hom.app V
  let sheafDesc : ((presheafToSheaf K A).obj (G.op.lan.obj P.obj)).obj.obj V ⟶
      ((presheafToSheaf K A).obj Q.obj).obj.obj V :=
    ((presheafToSheaf K A).map k.hom).hom.app V
  let targetUnit : Q.obj.obj V ⟶ ((presheafToSheaf K A).obj Q.obj).obj.obj V :=
    (toSheafify K Q.obj).app V
  let targetInv : ((presheafToSheaf K A).obj Q.obj).obj.obj V ⟶ Q.obj.obj V :=
    (sheafificationIso Q).inv.hom.app V
  have hSource : sourceUnit ≫ chosenMap = kanUnit ≫ sheafUnit := huU
  have hDesc : kanUnit ≫ descMap = α.app U := hk
  have hSheaf : sheafUnit ≫ sheafDesc = descMap ≫ targetUnit := hn
  have hTarget : targetUnit ≫ targetInv = 𝟙 _ := hr
  change sourceUnit ≫ chosenMap ≫ sheafDesc ≫ targetInv = α.app U
  calc
    _ = (kanUnit ≫ sheafUnit) ≫ sheafDesc ≫ targetInv := by
      rw [← Category.assoc sourceUnit chosenMap, hSource]
    _ = kanUnit ≫ (sheafUnit ≫ sheafDesc) ≫ targetInv := by
      simp only [Category.assoc]
    _ = kanUnit ≫ (descMap ≫ targetUnit) ≫ targetInv := by rw [hSheaf]
    _ = (kanUnit ≫ descMap) ≫ (targetUnit ≫ targetInv) := by
      simp only [Category.assoc]
    _ = α.app U := by rw [hDesc, hTarget, Category.comp_id]

/-- Every component retains the actual original alpha value. -/
theorem sheafPullbackTargetIso_unit_app (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] (U : Cᵒᵖ) :
    ((G.sheafAdjunctionContinuous A J K).unit.app P).hom.app U ≫
      (sheafPullbackTargetIso G J K P Q α).hom.hom.app (G.op.obj U) = α.app U := by
  exact congrArg (fun f => f.hom.app U) (sheafPullbackTargetIso_unit G J K P Q α)

/-- The original alpha determines the original adjunct, as a whole map. -/
theorem sheafPullbackTargetIso_homEquiv (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] :
    (G.sheafAdjunctionContinuous A J K).homEquiv P Q
      (sheafPullbackTargetIso G J K P Q α).hom = ⟨α⟩ := by
  rw [Adjunction.homEquiv_unit, sheafPullbackTargetIso_unit]

/-- The same comparison is the adjoint of the actual original alpha. -/
theorem sheafPullbackTargetIso_adjoint (P : Sheaf J A) (Q : Sheaf K A)
    (α : P.obj ⟶ G.op ⋙ Q.obj) [Q.obj.IsLeftKanExtension α] :
    ((G.sheafAdjunctionContinuous A J K).homEquiv P Q).symm ⟨α⟩ =
      (sheafPullbackTargetIso G J K P Q α).hom := by
  apply ((G.sheafAdjunctionContinuous A J K).homEquiv P Q).injective
  rw [Equiv.apply_symm_apply, sheafPullbackTargetIso_homEquiv]

/-- The original source square gives coefficient naturality of these same maps. -/
theorem sheafPullbackTargetIso_naturality
    {P P' : Sheaf J A} {Q Q' : Sheaf K A}
    (α : P.obj ⟶ G.op ⋙ Q.obj) (α' : P'.obj ⟶ G.op ⋙ Q'.obj)
    [Q.obj.IsLeftKanExtension α] [Q'.obj.IsLeftKanExtension α']
    (p : P ⟶ P') (q : Q ⟶ Q')
    (hα : p.hom ≫ α' = α ≫ Functor.whiskerLeft G.op q.hom) :
    (G.sheafPullback A J K).map p ≫ (sheafPullbackTargetIso G J K P' Q' α').hom =
      (sheafPullbackTargetIso G J K P Q α).hom ≫ q := by
  apply ((G.sheafAdjunctionContinuous A J K).homEquiv P Q').injective
  rw [Adjunction.homEquiv_naturality_left, sheafPullbackTargetIso_homEquiv,
    Adjunction.homEquiv_naturality_right, sheafPullbackTargetIso_homEquiv]
  apply ObjectProperty.hom_ext
  exact hα

section Family

variable {E : Type cE} [Category.{hE} E]
  (P : E ⥤ Sheaf J A) (Q : E ⥤ Sheaf K A)
  (α : P ⟶ Q ⋙ G.sheafPushforwardContinuous A J K)
  [∀ X : E, (Q.obj X).obj.IsLeftKanExtension (α.app X).hom]

/-- The coefficient-natural target comparison, built from the same original alphas. -/
def sheafPullbackTargetNatIso : P ⋙ G.sheafPullback A J K ≅ Q :=
  NatIso.ofComponents
    (fun X => sheafPullbackTargetIso G J K (P.obj X) (Q.obj X) (α.app X).hom)
    (by
      intro X Y f
      exact sheafPullbackTargetIso_naturality G J K (α.app X).hom (α.app Y).hom
        (P.map f) (Q.map f) (congrArg (fun g => g.hom) (α.naturality f)))

/-- The full original natural-transformation unit equality. -/
theorem sheafPullbackTargetNatIso_unit :
    (Functor.rightUnitor P).inv ≫
      Functor.whiskerLeft P (G.sheafAdjunctionContinuous A J K).unit ≫
      (Functor.associator P (G.sheafPullback A J K)
        (G.sheafPushforwardContinuous A J K)).inv ≫
      Functor.whiskerRight (sheafPullbackTargetNatIso G J K P Q α).hom
        (G.sheafPushforwardContinuous A J K) = α := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
  exact sheafPullbackTargetIso_unit G J K (P.obj X) (Q.obj X) (α.app X).hom

/-- The corresponding original family adjunct identity at every coefficient. -/
theorem sheafPullbackTargetNatIso_homEquiv (X : E) :
    (G.sheafAdjunctionContinuous A J K).homEquiv (P.obj X) (Q.obj X)
      ((sheafPullbackTargetNatIso G J K P Q α).hom.app X) = α.app X :=
  sheafPullbackTargetIso_homEquiv G J K (P.obj X) (Q.obj X) (α.app X).hom

end Family

end CategoryTheory.Functor
