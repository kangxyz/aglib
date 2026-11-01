/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.BinaryOperation
public import Aglib.CategoryTheory.Sites.Representable.GroupHom
public import Aglib.CategoryTheory.Sites.Torsors.CartesianMaps

/-! # The original sheaf torsor and its represented categorical action

An actual carrier representation and full test inclusion recover action and
difference morphisms on the original products. Their finite equations follow
from the original sheaf action and unique transport, hence construct the existing
TorsorAction on every generalized point. Local nonemptiness remains a separate
covering-sieve input to the reverse sheaf construction. Both roundtrips keep the
same carrier representation and actual action values.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Sheaf.Torsor.Represented

universe w uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {J : GrothendieckTopology C}
  {H : Grp D} [IsCommMonObj H.X]
  {hH : Presheaf.IsSheaf J (CommutativeGroupSections.testPresheaf.{w} F H)}
  (P : Torsor (CommutativeGroupSections.testSheaf.{w} F J H hH))
  (Y : D) {hY : Presheaf.IsSheaf J (LiftedRestrictedYoneda.presheaf.{w} F Y)}
  (e : LiftedRestrictedYoneda.sheaf.{w} F J Y hY ≅ P.carrier)

/-- The original carrier representation evaluated at an actual test. -/
def sectionEquiv (U : C) : (F.obj U ⟶ Y) ≃ P.carrier.obj.obj (op U) where
  toFun x := e.hom.hom.app (op U) (ULift.up x)
  invFun x := (e.inv.hom.app (op U) x).down
  left_inv x := congrArg (fun q => (q.hom.app (op U) (ULift.up x)).down) e.hom_inv_id
  right_inv x := congrArg (fun q => q.hom.app (op U) x) e.inv_hom_id

theorem sectionEquiv_naturality {U V : C} (f : U ⟶ V) (x : F.obj V ⟶ Y) :
    sectionEquiv P Y e U (F.map f ≫ x) =
      P.carrier.obj.map f.op (sectionEquiv P Y e V x) :=
  congrArg (fun q => q (ULift.up x)) (e.hom.hom.naturality f.op)

/-- The actual sheaf action in its original represented section coordinates. -/
def testAction (U : C) (a : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) : F.obj U ⟶ Y :=
  (sectionEquiv P Y e U).symm
    (P.action (op U) (ULift.up (Additive.ofMul a)) (sectionEquiv P Y e U x))

/-- The original representation evaluates the same test action on original sections. -/
theorem testAction_section (U : C) (a : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) :
    e.hom.hom.app (op U) (ULift.up (testAction P Y e U a x)) =
      P.action (op U) (ULift.up (Additive.ofMul a))
        (e.hom.hom.app (op U) (ULift.up x)) :=
  (sectionEquiv P Y e U).apply_symm_apply _

theorem testAction_naturality {U V : C} (f : U ⟶ V)
    (a : F.obj V ⟶ H.X) (x : F.obj V ⟶ Y) :
    F.map f ≫ testAction P Y e V a x =
      testAction P Y e U (F.map f ≫ a) (F.map f ≫ x) := by
  let aV : (CommutativeGroupSections.testSheaf.{w} F J H hH).obj.obj (op V) :=
    ULift.up (Additive.ofMul a)
  let aU : (CommutativeGroupSections.testSheaf.{w} F J H hH).obj.obj (op U) :=
    ULift.up (Additive.ofMul (F.map f ≫ a))
  have ha : (CommutativeGroupSections.testSheaf.{w} F J H hH).obj.map f.op aV = aU := rfl
  have hp := P.naturality f.op aV (sectionEquiv P Y e V x)
  apply (sectionEquiv P Y e U).injective
  rw [sectionEquiv_naturality]
  simp only [testAction, Equiv.apply_symm_apply]
  change P.carrier.obj.map f.op (P.action (op V) aV (sectionEquiv P Y e V x)) =
    P.action (op U) aU (sectionEquiv P Y e U (F.map f ≫ x))
  rw [← ha, sectionEquiv_naturality]
  exact hp

theorem testAction_one (U : C) (x : F.obj U ⟶ Y) : testAction P Y e U 1 x = x := by
  apply (sectionEquiv P Y e U).injective
  simp only [testAction, Equiv.apply_symm_apply]
  exact P.zero_action _ _

theorem testAction_mul (U : C) (a b : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) :
    testAction P Y e U (a * b) x = testAction P Y e U a (testAction P Y e U b x) := by
  apply (sectionEquiv P Y e U).injective
  simp only [testAction, Equiv.apply_symm_apply]
  exact P.add_action _ _ _ _

/-- The unique test transporter is derived from the given original sheaf torsor. -/
theorem testAction_transport (U : C) (x y : F.obj U ⟶ Y) :
    ∃! a, testAction P Y e U a x = y := by
  obtain ⟨a, ha, hu⟩ := P.unique_transport (op U)
    (sectionEquiv P Y e U x) (sectionEquiv P Y e U y)
  refine ⟨a.down.toMul, ?_, ?_⟩
  · apply (sectionEquiv P Y e U).injective
    let a₀ : (CommutativeGroupSections.testSheaf.{w} F J H hH).obj.obj (op U) :=
      ULift.up (Additive.ofMul a.down.toMul)
    have ha₀ : a₀ = a := by cases a; rfl
    simp only [testAction, Equiv.apply_symm_apply]
    change P.action (op U) a₀ (sectionEquiv P Y e U x) = sectionEquiv P Y e U y
    rw [ha₀]
    exact ha
  · intro b hb
    have he := congrArg (sectionEquiv P Y e U) hb
    simp only [testAction, Equiv.apply_symm_apply] at he
    exact congrArg (fun a => a.down.toMul) (hu (ULift.up (Additive.ofMul b)) he)

/-- Positive transport on the same represented test sections. -/
def testDifference (U : C) (x y : F.obj U ⟶ Y) : F.obj U ⟶ H.X :=
  Classical.choose (testAction_transport P Y e U x y)

theorem testAction_difference (U : C) (x y : F.obj U ⟶ Y) :
    testAction P Y e U (testDifference P Y e U x y) x = y :=
  (Classical.choose_spec (testAction_transport P Y e U x y)).1

theorem testDifference_eq (U : C) (x y : F.obj U ⟶ Y) (a : F.obj U ⟶ H.X)
    (ha : testAction P Y e U a x = y) : testDifference P Y e U x y = a :=
  ((Classical.choose_spec (testAction_transport P Y e U x y)).2 a ha).symm

theorem testDifference_action (U : C) (a : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) :
    testDifference P Y e U x (testAction P Y e U a x) = a :=
  testDifference_eq P Y e U x _ a rfl

theorem testDifference_naturality {U V : C} (f : U ⟶ V) (x y : F.obj V ⟶ Y) :
    F.map f ≫ testDifference P Y e V x y =
      testDifference P Y e U (F.map f ≫ x) (F.map f ≫ y) := by
  symm
  apply testDifference_eq
  rw [← testAction_naturality, testAction_difference]

variable (UAction UDifference : C)
  (κAction : F.obj UAction ≅ H.X ⊗ Y)
  (κDifference : F.obj UDifference ≅ Y ⊗ Y)

/-- The actual action morphism is recovered on the original product test. -/
def actionMap : H.X ⊗ Y ⟶ Y :=
  RepresentableBinaryOperation.map F (testAction P Y e) UAction κAction

/-- The actual positive difference morphism is recovered on the original product test. -/
def differenceMap : Y ⊗ Y ⟶ H.X :=
  RepresentableBinaryOperation.map F (testDifference P Y e) UDifference κDifference

theorem actionMap_value [F.Full] (U : C) (a : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) :
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction) a x =
      testAction P Y e U a x :=
  RepresentableBinaryOperation.map_value F (testAction P Y e) UAction κAction
    (testAction_naturality P Y e) U a x

theorem differenceMap_value [F.Full] (U : C) (x y : F.obj U ⟶ Y) :
    CategoryTheory.TorsorAction.differenceOfMap
      (differenceMap P Y e UDifference κDifference) x y = testDifference P Y e U x y :=
  RepresentableBinaryOperation.map_value F (testDifference P Y e) UDifference κDifference
    (testDifference_naturality P Y e) U x y

variable (UCarrier UMultiply : C)
  (κCarrier : F.obj UCarrier ≅ Y)
  (κMultiply : F.obj UMultiply ≅ (H.X ⊗ H.X) ⊗ Y)

include κCarrier in
theorem action_one_diagram [F.Full] :
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction) 1 (𝟙 Y) = 𝟙 Y := by
  apply (cancel_epi κCarrier.hom).mp
  rw [CategoryTheory.TorsorAction.actOfMap_naturality, MonObj.comp_one, Category.comp_id,
    actionMap_value]
  exact testAction_one P Y e UCarrier κCarrier.hom

include κMultiply in
theorem action_mul_diagram [F.Full] :
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction)
      ((fst (H.X ⊗ H.X) Y ≫ fst H.X H.X) * (fst (H.X ⊗ H.X) Y ≫ snd H.X H.X))
      (snd (H.X ⊗ H.X) Y) =
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction)
      (fst (H.X ⊗ H.X) Y ≫ fst H.X H.X)
      (CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction)
        (fst (H.X ⊗ H.X) Y ≫ snd H.X H.X) (snd (H.X ⊗ H.X) Y)) := by
  apply (cancel_epi κMultiply.hom).mp
  rw [CategoryTheory.TorsorAction.actOfMap_naturality,
    CategoryTheory.TorsorAction.actOfMap_naturality,
    CategoryTheory.TorsorAction.actOfMap_naturality, MonObj.comp_mul]
  simp only [actionMap_value]
  exact testAction_mul P Y e UMultiply _ _ _

theorem action_difference_diagram [F.Full] :
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction)
      (CategoryTheory.TorsorAction.differenceOfMap
        (differenceMap P Y e UDifference κDifference) (fst Y Y) (snd Y Y)) (fst Y Y) =
      snd Y Y := by
  apply (cancel_epi κDifference.hom).mp
  rw [CategoryTheory.TorsorAction.actOfMap_naturality,
    CategoryTheory.TorsorAction.differenceOfMap_naturality,
    actionMap_value, differenceMap_value]
  exact testAction_difference P Y e UDifference _ _

theorem difference_action_diagram [F.Full] :
    CategoryTheory.TorsorAction.differenceOfMap (differenceMap P Y e UDifference κDifference)
      (snd H.X Y) (CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction)
        (fst H.X Y) (snd H.X Y)) = fst H.X Y := by
  apply (cancel_epi κAction.hom).mp
  rw [CategoryTheory.TorsorAction.differenceOfMap_naturality,
    CategoryTheory.TorsorAction.actOfMap_naturality, differenceMap_value, actionMap_value]
  exact testDifference_action P Y e UAction _ _

/-- Whole represented categorical action; every required finite equation has been derived. -/
def categoricalAction [F.Full] : TorsorAction H (toUnit Y) :=
  CategoryTheory.TorsorAction.ofCartesianMaps
    (actionMap P Y e UAction κAction) (differenceMap P Y e UDifference κDifference)
    (action_one_diagram P Y e UAction κAction UCarrier κCarrier)
    (action_mul_diagram P Y e UAction κAction UMultiply κMultiply)
    (action_difference_diagram P Y e UAction UDifference κAction κDifference)
    (difference_action_diagram P Y e UAction UDifference κAction κDifference)

/-- Exact original sheaf-action evaluation, before passing to geometric points. -/
theorem categoricalAction_section [F.Full] (U : C)
    (a : F.obj U ⟶ H.X) (x : F.obj U ⟶ Y) :
    e.hom.hom.app (op U) (ULift.up
      ((categoricalAction P Y e UAction UDifference κAction κDifference
        UCarrier UMultiply κCarrier κMultiply).act a x)) =
      P.action (op U) (ULift.up (Additive.ofMul a)) (e.hom.hom.app (op U) (ULift.up x)) := by
  change sectionEquiv P Y e U
    (CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction) a x) = _
  rw [actionMap_value]
  exact (sectionEquiv P Y e U).apply_symm_apply _

/-- The reverse construction uses the same lifted carrier and actual categorical action.
Local nonemptiness is the original covering-sieve condition, supplied independently. -/
def ofCategoricalAction (τ : TorsorAction H (toUnit Y))
    (hloc : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Y hY) U ∈ J U) :
    Torsor (CommutativeGroupSections.testSheaf.{w} F J H hH) where
  carrier := LiftedRestrictedYoneda.sheaf.{w} F J Y hY
  action _ a t := ULift.up (τ.act a.down.toMul t.down)
  zero_action _ t := by
    cases t
    apply congrArg ULift.up
    exact τ.one_act _
  add_action _ a b t := congrArg ULift.up (τ.mul_act _ _ _)
  naturality f a t := congrArg ULift.up (τ.naturality (F.map f.unop) _ _)
  unique_transport _ s t := by
    obtain ⟨a, ha, hu⟩ := τ.transport s.down t.down (toUnit_unique _ _)
    refine ⟨ULift.up (Additive.ofMul a), congrArg ULift.up ha, ?_⟩
    intro b hb
    apply ULift.ext
    exact congrArg Additive.ofMul (hu b.down.toMul (congrArg ULift.down hb))
  locally_nonempty := hloc

/-- The reverse construction keeps literally the original represented carrier sheaf. -/
theorem ofCategoricalAction_carrier (τ : TorsorAction H (toUnit Y))
    (hloc : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Y hY) U ∈ J U) :
    (ofCategoricalAction (hH := hH) Y τ hloc).carrier =
      LiftedRestrictedYoneda.sheaf.{w} F J Y hY := rfl

/-- The whole sheaf-torsor roundtrip has precisely the given carrier representation. -/
def sheafRoundtrip [F.Full]
    (hloc : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Y hY) U ∈ J U) :
    Torsor.Iso
      (ofCategoricalAction (hH := hH) Y
        (categoricalAction P Y e UAction UDifference κAction κDifference
          UCarrier UMultiply κCarrier κMultiply) hloc) P where
  carrierIso := e
  equivariant U a t :=
    categoricalAction_section P Y e UAction UDifference κAction κDifference
      UCarrier UMultiply κCarrier κMultiply U.unop a.down.toMul t.down

/-- Starting with an actual categorical action returns that same action on every point. -/
theorem categoricalRoundtrip [F.Full] (τ : TorsorAction H (toUnit Y))
    (hloc : ∀ U : C, nonemptySieve (LiftedRestrictedYoneda.sheaf.{w} F J Y hY) U ∈ J U) :
    categoricalAction (ofCategoricalAction (hH := hH) Y τ hloc) Y
      (eqToIso (ofCategoricalAction_carrier (hH := hH) Y τ hloc).symm)
      UAction UDifference κAction κDifference UCarrier UMultiply κCarrier κMultiply = τ := by
  apply TorsorAction.ext
  intro T a x
  change lift a x ≫ (κAction.inv ≫
    τ.act (κAction.hom ≫ fst H.X Y) (κAction.hom ≫ snd H.X Y)) = τ.act a x
  rw [← τ.naturality]
  rw [κAction.inv_hom_id_assoc]
  exact τ.comp_actionMap a x

section RelativeMaps

variable {K : Grp D} [IsCommMonObj K.X]
  {hK : Presheaf.IsSheaf J (CommutativeGroupSections.testPresheaf.{w} F K)}
  (Q : Torsor (CommutativeGroupSections.testSheaf.{w} F J K hK))
  (Z : D) {hZ : Presheaf.IsSheaf J (LiftedRestrictedYoneda.presheaf.{w} F Z)}
  (d : LiftedRestrictedYoneda.sheaf.{w} F J Z hZ ≅ Q.carrier)
  (q : H ⟶ K)
  (r : Torsor.Hom (show CommutativeGroupSections.testSheaf.{w} F J H hH ⟶
    CommutativeGroupSections.testSheaf.{w} F J K hK from
      ⟨CommutativeGroupSections.testMap.{w} F H K q⟩) P Q)

/-- The original relative carrier map is recovered by the complete test-Yoneda inverse. -/
def carrierMap : Y ⟶ Z :=
  LiftedRestrictedYoneda.preimageOfTest.{w} F UCarrier κCarrier
    (e.hom ≫ r.map ≫ d.inv).hom

/-- Exact original section evaluation of that same recovered carrier map. -/
theorem carrierMap_section [F.Full] (U : C) (x : F.obj U ⟶ Y) :
    d.hom.hom.app (op U) (ULift.up (x ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r)) =
      r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)) := by
  have hv := LiftedRestrictedYoneda.preimageOfTest_app.{w} F UCarrier κCarrier
    (e.hom ≫ r.map ≫ d.inv).hom (op U) x
  change ULift.up (x ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r) =
    d.inv.hom.app (op U) (r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x))) at hv
  rw [hv]
  exact congrArg (fun k : Q.carrier ⟶ Q.carrier => k.hom.app (op U)
    (r.map.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)))) d.inv_hom_id

/-- Equivariance is proved on every original test from the supplied sheaf torsor morphism. -/
theorem carrierMap_test_equivariant [F.Full] (U : C) (a : F.obj U ⟶ H.X)
    (x : F.obj U ⟶ Y) :
    testAction P Y e U a x ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r =
      testAction Q Z d U (a ≫ q.hom.hom)
        (x ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r) := by
  apply (sectionEquiv Q Z d U).injective
  change d.hom.hom.app (op U) (ULift.up _) = d.hom.hom.app (op U) (ULift.up _)
  rw [carrierMap_section, testAction_section, testAction_section, carrierMap_section]
  exact r.equivariant (op U) (ULift.up (Additive.ofMul a))
    (e.hom.hom.app (op U) (ULift.up x))

variable (VAction : C) (κTargetAction : F.obj VAction ≅ K.X ⊗ Z)

/-- Universal-product testing proves the whole original action-map square. -/
theorem carrierMap_actionMap [F.Full] :
    actionMap P Y e UAction κAction ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r =
      lift (fst H.X Y ≫ q.hom.hom)
        (snd H.X Y ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r) ≫
          actionMap Q Z d VAction κTargetAction := by
  apply (cancel_epi κAction.hom).mp
  have hv := carrierMap_test_equivariant P Y e UCarrier κCarrier Q Z d q r UAction
    (κAction.hom ≫ fst H.X Y) (κAction.hom ≫ snd H.X Y)
  rw [← actionMap_value P Y e UAction κAction,
    ← actionMap_value Q Z d VAction κTargetAction] at hv
  simpa only [CategoryTheory.TorsorAction.actOfMap, ← comp_lift, lift_fst_snd,
    Category.id_comp, Category.assoc] using hv

/-- The actual map square gives equivariance on every generalized point. -/
theorem carrierMap_equivariant [F.Full] {T : D} (a : T ⟶ H.X) (x : T ⟶ Y) :
    CategoryTheory.TorsorAction.actOfMap (actionMap P Y e UAction κAction) a x ≫
      carrierMap P Y e UCarrier κCarrier Q Z d q r =
    CategoryTheory.TorsorAction.actOfMap (actionMap Q Z d VAction κTargetAction)
      (a ≫ q.hom.hom) (x ≫ carrierMap P Y e UCarrier κCarrier Q Z d q r) := by
  have hv := congrArg (fun k => lift a x ≫ k)
    (carrierMap_actionMap P Y e UAction κAction UCarrier κCarrier Q Z d q r
      VAction κTargetAction)
  simpa only [CategoryTheory.TorsorAction.actOfMap, ← Category.assoc, comp_lift,
    lift_fst, lift_snd] using hv

end RelativeMaps

end CategoryTheory.Sheaf.Torsor.Represented
