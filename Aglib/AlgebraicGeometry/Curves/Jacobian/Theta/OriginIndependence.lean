/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Principal
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicTranslation
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Homogeneity

/-!
# Change of the original Abel origin

Compare the two whole positive/based degree-one identities on the same
original curve and Picard representative. Evaluation at the new origin
identifies their constant factor; cancellation through the original
component inclusion gives translation of the whole Abel curve morphism.
Under the original coherent-H1 bound, the same principal isomorphism gives
the actual dual geometry. The whole Poincare coaction, with its base factor
retained until the relative quotient, then makes original Abel pullback and
the original principal isomorphism independent of the rational origin.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

open Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (o' : Spec (.of k) ⟶ X.left) (ho' : o' ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem positiveCurveMorphism_eq_based_mul_constant :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    singleParameterMorphism X ≫ (positiveAbelMorphism X P R 1).hom =
      (jacobianCurveMorphism hX o ho P R ≫ identityComponentι P.obj) *
        (toUnit X ≫ picardPoint P R
          (classOf X.left (PointDivisor.positiveLineBundle X hX o ho))) := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let C := classOf X.left (PointDivisor.positiveLineBundle X hX o ho)
  have hc : singleParameterMorphism X ≫
      (toUnit (locallyNoetherianParameter X 1).obj ≫ picardPoint P R (1 • C)) =
        toUnit X ≫ picardPoint P R C := by
    change singleParameterMorphism X ≫
      (toUnit (parameter X.hom 1) ≫ picardPoint P R (1 • C)) = _
    rw [comp_toUnit_assoc, one_nsmul]
  have h := congrArg (fun v : parameter X.hom 1 ⟶ P.obj => singleParameterMorphism X ≫ v)
    (positiveAbelMorphism_eq_based_mul_constant hX o ho P R 1)
  refine h.trans ?_
  rw [MonObj.comp_mul]
  exact congrArg₂ (fun v w : X ⟶ P.obj => v * w)
    (jacobianCurveMorphism_comp_inclusion hX o ho P R).symm hc

local notation "J" => picardIdentityComponent X.hom P R

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original Abel morphism at a second origin is the original first
morphism translated by minus the first Abel value of that second origin.
This is a whole map equation over any field, with no dual or genus input. -/
theorem jacobianCurveMorphism_changeOrigin :
    letI := picardCommGrpObj X.hom P R
    jacobianCurveMorphism hX o' ho' P R =
      jacobianCurveMorphism hX o ho P R ≫
        (GrpObj.mulRight (((Over.homMk o' ho' : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
          jacobianCurveMorphism hX o ho P R)⁻¹)).hom := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let f := jacobianCurveMorphism hX o ho P R
  let f' := jacobianCurveMorphism hX o' ho' P R
  let j : J ⟶ P.obj := identityComponentι P.obj
  let u : 𝟙_ (Over (Spec (.of k))) ⟶ X := Over.homMk o' ho'
  let a := u ≫ f
  let c := picardPoint P R (classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
  let c' := picardPoint P R (classOf X.left (PointDivisor.positiveLineBundle X hX o' ho'))
  have H : (f ≫ j) * (toUnit X ≫ c) = (f' ≫ j) * (toUnit X ≫ c') :=
    (positiveCurveMorphism_eq_based_mul_constant hX o ho P R).symm.trans
      (positiveCurveMorphism_eq_based_mul_constant hX o' ho' P R)
  have hp : u ≫ f' = η[J] := jacobianCurveMorphism_pointed hX o' ho' P R
  have hi : η[J] ≫ j = η[P.obj] := IsMonHom.one_hom j
  have Hc : c' = (a ≫ j) * c := by
    have Hunit := congrArg (fun v : X ⟶ P.obj => u ≫ v) H
    simp only [MonObj.comp_mul, ← Category.assoc, hp, hi, comp_toUnit,
      toUnit_unit, Category.id_comp] at Hunit
    simpa only [MonObj.one_eq_one, one_mul] using Hunit.symm
  have hc : toUnit X ≫ c' = (toUnit X ≫ (a ≫ j)) * (toUnit X ≫ c) := by
    rw [Hc, MonObj.comp_mul]
  have Hprod : (f' ≫ j) * (toUnit X ≫ (a ≫ j)) = f ≫ j := by
    have H' := H.symm
    rw [hc, ← _root_.mul_assoc] at H'
    exact mul_right_cancel H'
  have HJ : f' * (toUnit X ≫ a) = f := by
    apply (cancel_mono j).mp
    rw [MonObj.mul_comp, Category.assoc]
    exact Hprod
  have Hinv : toUnit X ≫ a⁻¹ = (toUnit X ≫ a)⁻¹ := by
    rw [← one_div a, GrpObj.comp_div, MonObj.comp_one, one_div]
  change f' = f ≫ ((𝟙 J) * (toUnit J ≫ a⁻¹))
  rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Hinv, ← div_eq_mul_inv]
  exact (mul_div_cancel_right f' (toUnit X ≫ a)).symm.trans
    (congrArg (fun z : X ⟶ J => z / (toUnit X ≫ a)) HJ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem picardIdentityComponentPullback_translation_eq_id
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (B : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType B.obj.hom]
    [IsSeparated B.obj.hom]
    (RB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy B)
    [IsProper (picardIdentityComponent A.hom B RB).hom]
    [GeometricallyIntegral (picardIdentityComponent A.hom B RB).hom]
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    letI := picardCommGrpObj A.hom B RB
    picardIdentityComponentPullback B RB B RB (GrpObj.mulRight b).hom =
      𝟙 (picardIdentityComponent A.hom B RB) := by
  let := picardCommGrpObj A.hom B RB
  let D := picardIdentityComponent A.hom B RB
  let i : D ⟶ B.obj := picardIdentityComponentι A.hom B RB
  let : IsMonHom i := isMonHom_picardIdentityComponentι A.hom B RB
  have : IsLocallyNoetherian D.left := LocallyOfFiniteType.isLocallyNoetherian D.hom
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨D, inferInstance⟩
  let a := poincareClass A B RB
  let f : A ⟶ A := (GrpObj.mulRight b).hom
  let t : D ⟶ A := toUnit D ≫ b
  let u : D ⟶ D := picardIdentityComponentPullback B RB B RB f
  let q : PicardGroup (pullback A.hom D.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op D) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op D)).hom
  let E : Additive (D ⟶ B.obj) ≃+ (fppfPicardSheaf A.hom).obj.obj (op D) :=
    picardHomAddEquiv A.hom B RB T
  have ha : q a = E (Additive.ofMul i) := by
    have hi := poincarePullback_fppfClass A B RB (T := T) (𝟙 D)
    change q (classOf (pullback A.hom D.hom) (poincarePullback A B RB (𝟙 D)).bundle) =
      E (Additive.ofMul (𝟙 D ≫ i)) at hi
    have he : classOf (pullback A.hom D.hom)
        (poincarePullback A B RB (𝟙 D)).bundle = a :=
      Quotient.sound ⟨(poincarePullbackIdIso A B RB).iso⟩
    rw [he, Category.id_comp] at hi
    exact hi
  have hm : (f ⊗ₘ 𝟙 D) = universalTranslationMorphism A t (𝟙 D) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [tensorHom_fst, universalTranslationMorphism, lift_fst,
        translationFamilyMorphism]
      change fst A D ≫ ((𝟙 A) * (toUnit A ≫ b)) =
        (fst A D) * (snd A D ≫ (toUnit D ≫ b))
      rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, comp_toUnit_assoc]
    · simp only [tensorHom_snd, universalTranslationMorphism, lift_snd,
        Category.comp_id]
  have hmap : familyMapOfHom f D = (universalTranslationMorphism A t (𝟙 D)).left :=
    (familyMapOfHom_eq_tensorHom A f D).trans (congrArg Over.Hom.left hm)
  have hid : translationFamilyMap A (𝟙 D) = 𝟙 (A ⊗ D) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [translationFamilyMap]
  have qbase (c : PicardGroup D.left) :
      q (pullbackClass (pullback.snd A.hom D.hom) c) = 0 := by
    change ((toFppfPicardSheaf A.hom).app (op D)).hom
      (((quotientProjection A.hom).app (op D)).hom
        (((basePullback A.hom).app (op D)).hom c)) = 0
    rw [quotientProjection_basePullback_apply, map_zero]
  have hclass : q (pullbackClass (familyMapOfHom f D) a) = q a := by
    have H := congrArg q (poincareTranslationClass_eq_basePullback A B RB t (𝟙 D))
    rw [universalTranslationClass, ← hmap, hid, Over.id_left, pullbackClass_id,
      map_sub, qbase] at H
    exact sub_eq_zero.mp H
  have hdual := homEquiv_comp_picardIdentityComponentPullback B RB B RB f
    (T := T) (𝟙 D)
  change E (Additive.ofMul ((𝟙 D ≫ u) ≫ i)) =
    ((fppfPicardPullback f).hom.app (op D)).hom
      (E (Additive.ofMul (𝟙 D ≫ i))) at hdual
  simp only [Category.id_comp] at hdual
  have hsource := fppfPicardPullback_class f D a
  change q (pullbackClass (familyMapOfHom f D) a) =
    ((fppfPicardPullback f).hom.app (op D)).hom (q a) at hsource
  have heq : E (Additive.ofMul (u ≫ i)) = E (Additive.ofMul i) := by
    calc
      _ = ((fppfPicardPullback f).hom.app (op D)).hom
          (E (Additive.ofMul i)) := hdual
      _ = ((fppfPicardPullback f).hom.app (op D)).hom (q a) := by rw [ha]
      _ = q (pullbackClass (familyMapOfHom f D) a) := hsource.symm
      _ = q a := hclass
      _ = _ := ha
  change u = 𝟙 D
  apply (cancel_mono i).mp
  simpa only [Category.id_comp, toMul_ofMul] using congrArg Additive.toMul (E.injective heq)

variable [IsAlgClosed k] [IsSeparated P.obj.hom]
  (Q : LocallyNoetherianOver (Spec (.of k)))
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original Abel pullback on the same Picard identity components is
independent of the rational origin, under the original coherent-H1 bound.
The dual component's geometry is derived from the same actual theta Iso. -/
theorem picardIdentityComponentPullback_jacobianCurveMorphism_changeOrigin
    (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    letI := picardCommGrpObj (J).hom Q RQ
    picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o' ho' P R) =
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let D := picardIdentityComponent (J).hom Q RQ
  let e : J ≅ D := thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1
  have : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.inv))
  have : IsProper D.hom := by
    rw [← Over.w e.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.inv.left (J).hom).mpr
      inferInstance
  have : GeometricallyIntegral D.hom := by
    rw [← Over.w e.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral
      e.inv.left (J).hom).mpr inferInstance
  let a := (Over.homMk o' ho' : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
    jacobianCurveMorphism hX o ho P R
  have ht := picardIdentityComponentPullback_translation_eq_id J Q RQ a⁻¹
  rw [jacobianCurveMorphism_changeOrigin hX o ho o' ho' P R,
    picardIdentityComponentPullback_comp P R Q RQ Q RQ, ht, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original theta principal isomorphism does not depend on the
rational origin, retaining exactly the current original coherent-H1 premise. -/
theorem thetaPrincipalIsoOfStructureH1Le_changeOrigin (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    thetaPrincipalIsoOfStructureH1Le hX o' ho' P R Q RQ hg hH1 =
      thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1 := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let D := picardIdentityComponent (J).hom Q RQ
  let e : J ≅ D := thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1
  let e' : J ≅ D := thetaPrincipalIsoOfStructureH1Le hX o' ho' P R Q RQ hg hH1
  have hp := picardIdentityComponentPullback_jacobianCurveMorphism_changeOrigin
    hX o ho o' ho' P R Q RQ hg hH1
  have hi : e'.inv = e.inv :=
    (thetaPrincipalIsoOfStructureH1Le_inv hX o' ho' P R Q RQ hg hH1).trans
      ((congrArg (fun v : D ⟶ J => v ≫ ι[J]) hp).trans
        (thetaPrincipalIsoOfStructureH1Le_inv hX o ho P R Q RQ hg hH1).symm)
  change e' = e
  apply Iso.ext
  apply (cancel_mono e.inv).mp
  calc
    e'.hom ≫ e.inv = e'.hom ≫ e'.inv := congrArg (fun v : D ⟶ J => e'.hom ≫ v) hi.symm
    _ = 𝟙 J := Iso.hom_inv_id e'
    _ = e.hom ≫ e.inv := (Iso.hom_inv_id e).symm

end AlgebraicGeometry.Scheme.OverField.Curve
