/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsors.CartesianMaps
public import Aglib.CategoryTheory.Sites.Torsors.AdjointPullback

/-! # Whole descent of the original action through full faithful represented tests

The given functor square is the actual restriction square. Fullness constructs
the original lifted action and positive difference maps, while faithfulness
reflects their finite-product equations. Those equations construct the existing
TorsorAction on all ambient generalized points. The original Hom adjunction,
when supplied, proves the whole pullback roundtrip. No descended action,
surjectivity or desired action equality is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.TorsorAction.Descent

universe uB vB uE vE uC vC uD vD
variable {B : Type uB} [Category.{vB} B] {E : Type uE} [Category.{vE} E]
  {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D]
  (I : B ⥤ C) (J : E ⥤ D) (G : B ⥤ E) (F : C ⥤ D)
  [I.Full] [J.Full] [J.Faithful] [G.Full] [G.Faithful] [F.Monoidal]
  (β : I ⋙ F ≅ G ⋙ J)

/-- Fullness lifts the actual ambient arrow through the actual restriction square. -/
def liftedArrow (U V : B) (q : F.obj (I.obj U) ⟶ F.obj (I.obj V)) : I.obj U ⟶ I.obj V :=
  I.map (G.preimage (J.preimage (β.inv.app U ≫ q ≫ β.hom.app V)))

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  [I.Full] [J.Faithful] [G.Faithful] [F.Monoidal] in
/-- The lifted arrow has exactly the original mapped value. -/
theorem map_liftedArrow (U V : B) (q : F.obj (I.obj U) ⟶ F.obj (I.obj V)) :
    F.map (liftedArrow I J G F β U V q) = q := by
  let r := G.preimage (J.preimage (β.inv.app U ≫ q ≫ β.hom.app V))
  apply (cancel_mono (β.hom.app V)).mp
  have h := β.hom.naturality r
  change F.map (I.map r) ≫ β.hom.app V = β.hom.app U ≫ J.map (G.map r) at h
  rw [G.map_preimage, J.map_preimage] at h
  rw [← Category.assoc (β.hom.app U) (β.inv.app U), β.hom_inv_id_app,
    Category.id_comp] at h
  exact h

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  [J.Full] [G.Full] [F.Monoidal] in
include β in
/-- Faithfulness reflects equality on the original represented source/target objects. -/
theorem map_injective {U V : B} {a b : I.obj U ⟶ I.obj V} (h : F.map a = F.map b) : a = b := by
  have hβ : J.map (G.map (I.preimage a)) = J.map (G.map (I.preimage b)) := by
    apply (cancel_epi (β.hom.app U)).mp
    calc
      _ = F.map (I.map (I.preimage a)) ≫ β.hom.app V :=
        (β.hom.naturality (I.preimage a)).symm
      _ = F.map a ≫ β.hom.app V := by rw [I.map_preimage]
      _ = F.map b ≫ β.hom.app V := congrArg (fun k => k ≫ β.hom.app V) h
      _ = β.hom.app U ≫ J.map (G.map (I.preimage b)) := by
        simpa only [Functor.comp_map, I.map_preimage] using
          β.hom.naturality (I.preimage b)
  have hab := G.map_injective (J.map_injective hβ)
  exact (I.map_preimage a).symm.trans ((congrArg I.map hab).trans (I.map_preimage b))

variable (A : Grp C) (Y : B)
  (τ : TorsorAction (F.mapGrp.obj A) (toUnit (F.obj (I.obj Y))))
  (HC : B) (κH : I.obj HC ≅ A.X)
  (UAction UDifference : B)
  (κAction : I.obj UAction ≅ A.X ⊗ I.obj Y)
  (κDifference : I.obj UDifference ≅ I.obj Y ⊗ I.obj Y)

/-- The complete original action lift through the native product comparison. -/
def actionMap : A.X ⊗ I.obj Y ⟶ I.obj Y :=
  let mτ : F.obj A.X ⊗ F.obj (I.obj Y) ⟶ F.obj (I.obj Y) := τ.actionMap
  κAction.inv ≫ liftedArrow I J G F β UAction Y
    (F.map κAction.hom ≫ prodComparison F A.X (I.obj Y) ≫ mτ)

/-- The complete original positive-difference lift through the native product comparison. -/
def differenceMap : I.obj Y ⊗ I.obj Y ⟶ A.X :=
  let dτ : F.obj (I.obj Y) ⊗ F.obj (I.obj Y) ⟶ F.obj A.X := τ.positiveDifferenceMap
  κDifference.inv ≫ liftedArrow I J G F β UDifference HC
    (F.map κDifference.hom ≫ prodComparison F (I.obj Y) (I.obj Y) ≫
      dτ ≫ F.map κH.inv) ≫ κH.hom

omit [I.Full] [J.Faithful] [G.Faithful] in
/-- The entire action morphism retains its original target value. -/
theorem map_actionMap :
    F.map (actionMap I J G F β A Y τ UAction κAction) =
      prodComparison F A.X (I.obj Y) ≫ τ.actionMap := by
  let mτ : F.obj A.X ⊗ F.obj (I.obj Y) ⟶ F.obj (I.obj Y) := τ.actionMap
  change F.map (κAction.inv ≫ liftedArrow I J G F β UAction Y
    (F.map κAction.hom ≫ prodComparison F A.X (I.obj Y) ≫ mτ)) =
      prodComparison F A.X (I.obj Y) ≫ mτ
  rw [F.map_comp, map_liftedArrow]
  rw [← Category.assoc (F.map κAction.inv) (F.map κAction.hom), ← F.map_comp,
    κAction.inv_hom_id, F.map_id, Category.id_comp]

omit [I.Full] [J.Faithful] [G.Faithful] in
/-- The entire difference morphism retains its original positive transport value. -/
theorem map_differenceMap :
    F.map (differenceMap I J G F β A Y τ HC κH UDifference κDifference) =
      prodComparison F (I.obj Y) (I.obj Y) ≫ τ.positiveDifferenceMap := by
  let dτ : F.obj (I.obj Y) ⊗ F.obj (I.obj Y) ⟶ F.obj A.X := τ.positiveDifferenceMap
  change F.map (κDifference.inv ≫ liftedArrow I J G F β UDifference HC
    (F.map κDifference.hom ≫ prodComparison F (I.obj Y) (I.obj Y) ≫
      dτ ≫ F.map κH.inv) ≫ κH.hom) = prodComparison F (I.obj Y) (I.obj Y) ≫ dτ
  simp only [F.map_comp]
  rw [map_liftedArrow]
  simp only [Category.assoc]
  rw [← F.map_comp, κH.inv_hom_id, F.map_id, Category.comp_id]
  rw [← Category.assoc (F.map κDifference.inv) (F.map κDifference.hom), ← F.map_comp,
    κDifference.inv_hom_id, F.map_id, Category.id_comp]

omit [F.Monoidal] in
private theorem map_lift_comparison {T U V : C} (a : T ⟶ U) (b : T ⟶ V) :
    F.map (lift a b) ≫ prodComparison F U V = lift (F.map a) (F.map b) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

omit [I.Full] [J.Faithful] [G.Faithful] in
/-- Actual mapped point values of the lifted action. -/
theorem map_act {T : C} (a : T ⟶ A.X) (x : T ⟶ I.obj Y) :
    F.map (actOfMap (actionMap I J G F β A Y τ UAction κAction) a x) =
      τ.act (F.map a) (F.map x) := by
  let mτ : F.obj A.X ⊗ F.obj (I.obj Y) ⟶ F.obj (I.obj Y) := τ.actionMap
  have hm : F.map (actionMap I J G F β A Y τ UAction κAction) =
      prodComparison F A.X (I.obj Y) ≫ mτ :=
    map_actionMap I J G F β A Y τ UAction κAction
  change F.map (lift a x ≫ actionMap I J G F β A Y τ UAction κAction) = _
  calc
    _ = F.map (lift a x) ≫ F.map (actionMap I J G F β A Y τ UAction κAction) :=
      F.map_comp _ _
    _ = F.map (lift a x) ≫ (prodComparison F A.X (I.obj Y) ≫ mτ) :=
      congrArg (fun k => F.map (lift a x) ≫ k) hm
    _ = lift (F.map a) (F.map x) ≫ mτ := by rw [← Category.assoc, map_lift_comparison]
    _ = τ.act (F.map a) (F.map x) := τ.comp_actionMap _ _

omit [I.Full] [J.Faithful] [G.Faithful] in
/-- Actual mapped point values of the lifted positive difference. -/
theorem map_difference {T : C} (x y : T ⟶ I.obj Y) :
    F.map (differenceOfMap (differenceMap I J G F β A Y τ HC κH UDifference κDifference) x y) =
      τ.positiveTransport (F.map x) (F.map y) := by
  let dτ : F.obj (I.obj Y) ⊗ F.obj (I.obj Y) ⟶ F.obj A.X := τ.positiveDifferenceMap
  let tτ : F.obj T ⟶ F.obj A.X := τ.positiveTransport (F.map x) (F.map y)
  have hd : F.map (differenceMap I J G F β A Y τ HC κH UDifference κDifference) =
      prodComparison F (I.obj Y) (I.obj Y) ≫ dτ :=
    map_differenceMap I J G F β A Y τ HC κH UDifference κDifference
  change F.map (lift x y ≫ differenceMap I J G F β A Y τ HC κH UDifference κDifference) = tτ
  calc
    _ = F.map (lift x y) ≫ F.map (differenceMap I J G F β A Y τ HC κH UDifference κDifference) :=
      F.map_comp _ _
    _ = F.map (lift x y) ≫ (prodComparison F (I.obj Y) (I.obj Y) ≫ dτ) :=
      congrArg (fun k => F.map (lift x y) ≫ k) hd
    _ = lift (F.map x) (F.map y) ≫ dτ := by rw [← Category.assoc, map_lift_comparison]
    _ = tτ := by
      change lift (F.map x) (F.map y) ≫ τ.positiveDifferenceMap =
        τ.positiveTransport (F.map x) (F.map y)
      exact τ.comp_positiveDifferenceMap _ _

theorem finite_one (U : B) (x : I.obj U ⟶ I.obj Y) :
    actOfMap (actionMap I J G F β A Y τ UAction κAction) 1 x = x := by
  apply map_injective I J G F β (U := U) (V := Y)
  rw [map_act, F.map_one]
  exact τ.one_act _

theorem finite_mul (U : B) (a b : I.obj U ⟶ A.X) (x : I.obj U ⟶ I.obj Y) :
    actOfMap (actionMap I J G F β A Y τ UAction κAction) (a * b) x =
      actOfMap (actionMap I J G F β A Y τ UAction κAction) a
        (actOfMap (actionMap I J G F β A Y τ UAction κAction) b x) := by
  apply map_injective I J G F β (U := U) (V := Y)
  rw [map_act, map_act, map_act, F.map_mul]
  exact τ.mul_act _ _ _

theorem finite_difference (U : B) (x y : I.obj U ⟶ I.obj Y) :
    actOfMap (actionMap I J G F β A Y τ UAction κAction)
      (differenceOfMap (differenceMap I J G F β A Y τ HC κH UDifference κDifference) x y) x =
      y := by
  apply map_injective I J G F β (U := U) (V := Y)
  rw [map_act, map_difference, τ.act_positiveTransport]

theorem finite_recover (U : B) (a : I.obj U ⟶ A.X) (x : I.obj U ⟶ I.obj Y) :
    differenceOfMap (differenceMap I J G F β A Y τ HC κH UDifference κDifference) x
      (actOfMap (actionMap I J G F β A Y τ UAction κAction) a x) = a := by
  apply (cancel_mono κH.inv).mp
  apply map_injective I J G F β (U := U) (V := HC)
  rw [F.map_comp, F.map_comp, map_difference, map_act]
  exact congrArg (fun k : F.obj (I.obj U) ⟶ (F.mapGrp.obj A).X => k ≫ F.map κH.inv)
    (τ.positiveTransport_act (F.map a) (F.map x))

variable (UMultiply : B) (κMultiply : I.obj UMultiply ≅ (A.X ⊗ A.X) ⊗ I.obj Y)

include κMultiply in
theorem action_mul_diagram :
    actOfMap (actionMap I J G F β A Y τ UAction κAction)
      ((fst (A.X ⊗ A.X) (I.obj Y) ≫ fst A.X A.X) *
        (fst (A.X ⊗ A.X) (I.obj Y) ≫ snd A.X A.X)) (snd (A.X ⊗ A.X) (I.obj Y)) =
      actOfMap (actionMap I J G F β A Y τ UAction κAction)
        (fst (A.X ⊗ A.X) (I.obj Y) ≫ fst A.X A.X)
        (actOfMap (actionMap I J G F β A Y τ UAction κAction)
          (fst (A.X ⊗ A.X) (I.obj Y) ≫ snd A.X A.X) (snd (A.X ⊗ A.X) (I.obj Y))) := by
  apply (cancel_epi κMultiply.hom).mp
  rw [actOfMap_naturality, actOfMap_naturality, actOfMap_naturality, MonObj.comp_mul]
  exact finite_mul I J G F β A Y τ UAction κAction UMultiply _ _ _

theorem action_difference_diagram :
    actOfMap (actionMap I J G F β A Y τ UAction κAction)
      (differenceOfMap (differenceMap I J G F β A Y τ HC κH UDifference κDifference)
        (fst (I.obj Y) (I.obj Y)) (snd (I.obj Y) (I.obj Y))) (fst (I.obj Y) (I.obj Y)) =
      snd (I.obj Y) (I.obj Y) := by
  apply (cancel_epi κDifference.hom).mp
  rw [actOfMap_naturality, differenceOfMap_naturality]
  exact finite_difference I J G F β A Y τ HC κH UAction UDifference κAction κDifference
    UDifference _ _

theorem difference_action_diagram :
    differenceOfMap (differenceMap I J G F β A Y τ HC κH UDifference κDifference)
      (snd A.X (I.obj Y)) (actOfMap (actionMap I J G F β A Y τ UAction κAction)
        (fst A.X (I.obj Y)) (snd A.X (I.obj Y))) = fst A.X (I.obj Y) := by
  apply (cancel_epi κAction.hom).mp
  rw [differenceOfMap_naturality, actOfMap_naturality]
  exact finite_recover I J G F β A Y τ HC κH UAction UDifference κAction κDifference
    UAction _ _

/-- The whole descended action on every ambient point follows from the lifted maps. -/
def action : TorsorAction A (toUnit (I.obj Y)) :=
  ofCartesianMaps (actionMap I J G F β A Y τ UAction κAction)
    (differenceMap I J G F β A Y τ HC κH UDifference κDifference)
    (finite_one I J G F β A Y τ UAction κAction Y (𝟙 (I.obj Y)))
    (action_mul_diagram I J G F β A Y τ UAction κAction UMultiply κMultiply)
    (action_difference_diagram I J G F β A Y τ HC κH UAction UDifference κAction κDifference)
    (difference_action_diagram I J G F β A Y τ HC κH UAction UDifference κAction κDifference)

/-- The same actual adjunction recovers the full original target action, not only image points. -/
theorem pullback_action {L : D ⥤ C} (adj : L ⊣ F) :
    TorsorAction.pullback adj A (I.obj Y)
      (action I J G F β A Y τ HC κH UAction UDifference κAction κDifference
        UMultiply κMultiply) = τ := by
  apply TorsorAction.ext
  intro T a x
  change adj.unit.app T ≫ F.map
    (actOfMap (actionMap I J G F β A Y τ UAction κAction)
      ((TorsorAction.adjointPointMulEquiv adj T A).symm a)
      ((adj.homEquiv T (I.obj Y)).symm x)) = τ.act a x
  rw [map_act]
  refine (τ.naturality (adj.unit.app T) _ _).trans ?_
  change τ.act
    (TorsorAction.adjointPointMulEquiv adj T A
      ((TorsorAction.adjointPointMulEquiv adj T A).symm a))
    (adj.homEquiv T (I.obj Y) ((adj.homEquiv T (I.obj Y)).symm x)) = τ.act a x
  rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

end CategoryTheory.TorsorAction.Descent
