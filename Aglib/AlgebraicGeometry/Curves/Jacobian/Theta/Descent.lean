/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.OriginIndependence
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.GenusZero
public import Aglib.AlgebraicGeometry.RationalPoint.SurjectiveLift
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Projectivity
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Multiplication
public import Aglib.AlgebraicGeometry.Picard.FppfSections
public import Aglib.AlgebraicGeometry.Sites.FppfQuotient
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve

/-!
# The original Abel difference without a rational origin

The existing positive degree-one classifier gives a whole difference map
on the original curve times itself. Its diagonal is the original unit, so
connectedness factors it through the same original Jacobian component.
The product-difference cocycle is a whole morphism equation on arbitrary
tests; it does not use representation on non-Noetherian tests.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

open Abel.BoundedFamily

private theorem geometricallyIntegral_product
    {k : Type u} [Field k] (V W : FScheme k)
    [IsProper V.hom] [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom] :
    GeometricallyIntegral (V ⊗ W).hom := by
  constructor
  intro L _ y Z f g hs
  let F := Over.pullback y
  have hVW : IsIntegral (F.obj V ⊗ F.obj W).left := by dsimp [F]; infer_instance
  have : IsIntegral ((Over.forget (Spec (.of L))).obj (F.obj V ⊗ F.obj W)) := hVW
  let e := (Over.forget (Spec (.of L))).mapIso (Functor.Monoidal.μIso F V W)
  have : IsIntegral (pullback (V ⊗ W).hom y) := IsIntegral.of_isIso e.hom
  exact IsIntegral.of_isIso hs.isoPullback.inv

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

/-- The original positive degree-one classifier on the original curve,
without selecting a rational origin or a second parameter realization. -/
def positiveCurveMorphism : X ⟶ P.obj := by
  let := hX.smooth
  let := hX.proper
  exact singleParameterMorphism X ≫ (positiveAbelMorphism X P R 1).hom

/-- Whole original Picard difference, before its component factorization. -/
def curveDifferencePicardMorphism :
    letI := picardCommGrpObj X.hom P R
    X ⊗ X ⟶ P.obj :=
  letI := picardCommGrpObj X.hom P R
  (fst X X ≫ positiveCurveMorphism hX P R) /
    (snd X X ≫ positiveCurveMorphism hX P R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire diagonal, not only its field points, maps to the unit. -/
theorem curveDifferencePicardMorphism_diagonal :
    letI := picardCommGrpObj X.hom P R
    lift (𝟙 X) (𝟙 X) ≫ curveDifferencePicardMorphism hX P R = 1 := by
  let := picardCommGrpObj X.hom P R
  simp only [curveDifferencePicardMorphism, GrpObj.comp_div, ← Category.assoc,
    lift_fst, lift_snd, Category.id_comp, div_self']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Connectedness and the whole diagonal law put the actual image in the
original open identity component. No curve rational point is chosen. -/
theorem curveDifferencePicardMorphism_range :
    letI := picardCommGrpObj X.hom P R
    Set.range (curveDifferencePicardMorphism hX P R).left ⊆ identityComponent P.obj := by
  let := hX.smooth
  let := hX.proper
  let := hX.connected
  let := picardCommGrpObj X.hom P R
  have : GeometricallyIntegral X.hom :=
    geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected X.hom
  have : GeometricallyIntegral (X ⊗ X).hom := geometricallyIntegral_product X X
  have : IsIntegral (X ⊗ X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (X ⊗ X).hom
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  obtain ⟨x⟩ := (inferInstance : Nonempty X.left)
  let δ : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)
  apply range_subset_identityComponent P.obj (curveDifferencePicardMorphism hX P R).left
    (δ.left x)
  have H := congrArg (fun v : X ⟶ P.obj => v.left x)
    (curveDifferencePicardMorphism_diagonal hX P R)
  refine H.trans ?_
  change η[P.obj].left ((toUnit X).left x) = Scheme.Group.unitPoint P.obj
  exact Scheme.Group.one_left_apply P.obj _

/-- The point-free original Abel difference in the SAME original J. -/
def jacobianDifferenceMorphism :
    letI := picardCommGrpObj X.hom P R
    X ⊗ X ⟶ picardIdentityComponent X.hom P R := by
  let := picardCommGrpObj X.hom P R
  exact liftIdentityComponent P.obj (curveDifferencePicardMorphism hX P R)
    (curveDifferencePicardMorphism_range hX P R)

@[reassoc]
theorem jacobianDifferenceMorphism_comp_inclusion :
    letI := picardCommGrpObj X.hom P R
    jacobianDifferenceMorphism hX P R ≫ identityComponentι P.obj =
      curveDifferencePicardMorphism hX P R := by
  let := picardCommGrpObj X.hom P R
  exact liftIdentityComponent_ι P.obj _ (curveDifferencePicardMorphism_range hX P R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual component-valued difference retains the whole diagonal law. -/
theorem jacobianDifferenceMorphism_diagonal :
    letI := picardCommGrpObj X.hom P R
    lift (𝟙 X) (𝟙 X) ≫ jacobianDifferenceMorphism hX P R = 1 := by
  let := picardCommGrpObj X.hom P R
  apply (cancel_mono (identityComponentι P.obj)).mp
  rw [Category.assoc, jacobianDifferenceMorphism_comp_inclusion,
    curveDifferencePicardMorphism_diagonal, MonObj.one_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original difference cocycle is equality of whole morphisms on
arbitrary tests, including nonreduced and non-Noetherian schemes. -/
theorem jacobianDifferenceMorphism_cocycle {T : FScheme k} (x y z : T ⟶ X) :
    letI := picardCommGrpObj X.hom P R
    lift x z ≫ jacobianDifferenceMorphism hX P R =
      (lift x y ≫ jacobianDifferenceMorphism hX P R) /
        (lift z y ≫ jacobianDifferenceMorphism hX P R) := by
  let := picardCommGrpObj X.hom P R
  apply (cancel_mono (identityComponentι P.obj)).mp
  simp only [GrpObj.div_comp, Category.assoc, jacobianDifferenceMorphism_comp_inclusion]
  simp only [curveDifferencePicardMorphism, GrpObj.comp_div, ← Category.assoc,
    lift_fst, lift_snd]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, _root_.mul_assoc, inv_mul_cancel_left]

local notation "J" => picardIdentityComponent X.hom P R

variable (Q : LocallyNoetherianOver (Spec (.of k)))
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  [LocallyOfFiniteType Q.obj.hom]

local notation "D" => picardIdentityComponent (Over.hom (picardIdentityComponent X.hom P R)) Q RQ

/-- The original difference family into the SAME J times D, with the
origin allowed to vary on an arbitrary test scheme. -/
def jacobianDifferenceFamilyMorphism (T : FScheme k) (d : T ⟶ D) (y : T ⟶ X) :
    X ⊗ T ⟶ J ⊗ D :=
  lift ((lift (fst X T) (snd X T ≫ y)) ≫ jacobianDifferenceMorphism hX P R)
    (snd X T ≫ d)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole parameter naturality of the original difference family. -/
theorem jacobianDifferenceFamilyMorphism_naturality {T T' : FScheme k} (f : T' ⟶ T)
    (d : T ⟶ D) (y : T ⟶ X) :
    translationFamilyMap X f ≫ jacobianDifferenceFamilyMorphism hX P R Q RQ T d y =
      jacobianDifferenceFamilyMorphism hX P R Q RQ T' (f ≫ d) (f ≫ y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [jacobianDifferenceFamilyMorphism, Category.assoc, lift_fst]
    rw [CartesianMonoidalCategory.comp_lift_assoc]
    simp only [translationFamilyMap, lift_fst, lift_snd_assoc, Category.assoc]
  · simp only [jacobianDifferenceFamilyMorphism, Category.assoc, lift_snd]
    simp only [translationFamilyMap, lift_snd_assoc, Category.assoc]

variable [IsSeparated P.obj.hom]

/-- The class of the SAME selected original Poincare bundle of J, with
source geometry derived from the original curve and no extra origin. -/
def jacobianPoincareClass : PicardGroup (pullback (J).hom (D).hom) := by
  let := picardCommGrpObj X.hom P R
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  exact poincareClass J Q RQ

/-- The original Poincare class pulled to the curve by the actual
point-free difference family. No curve origin or H1 premise is chosen. -/
def jacobianDifferenceFamilyClass (T : FScheme k) (d : T ⟶ D) (y : T ⟶ X) :
    PicardGroup (pullback X.hom T.hom) :=
  pullbackClass (jacobianDifferenceFamilyMorphism hX P R Q RQ T d y).left
    (jacobianPoincareClass hX P R Q RQ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole original family class commutes with every parameter map,
including maps from nonreduced or non-Noetherian tests. -/
theorem jacobianDifferenceFamilyClass_naturality {T T' : FScheme k} (f : T' ⟶ T)
    (d : T ⟶ D) (y : T ⟶ X) :
    pullbackClass ((familyScheme X.hom).map f)
        (jacobianDifferenceFamilyClass hX P R Q RQ T d y) =
      jacobianDifferenceFamilyClass hX P R Q RQ T' (f ≫ d) (f ≫ y) := by
  have hm := congrArg Over.Hom.left
    (jacobianDifferenceFamilyMorphism_naturality hX P R Q RQ f d y)
  change (translationFamilyMap X f).left ≫
      (jacobianDifferenceFamilyMorphism hX P R Q RQ T d y).left =
        (jacobianDifferenceFamilyMorphism hX P R Q RQ T' (f ≫ d) (f ≫ y)).left at hm
  rw [translationFamilyMap_left] at hm
  change pullbackClass ((familyScheme X.hom).map f)
      (pullbackClass (jacobianDifferenceFamilyMorphism hX P R Q RQ T d y).left
        (jacobianPoincareClass hX P R Q RQ)) = _
  rw [← pullbackClass_comp]
  exact congrArg (fun v => pullbackClass v (jacobianPoincareClass hX P R Q RQ)) hm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire parameter-unit family class vanishes, without selecting
an origin on the curve. -/
theorem jacobianDifferenceFamilyClass_parameter_one (T : FScheme k) (y : T ⟶ X) :
    jacobianDifferenceFamilyClass hX P R Q RQ T (1 : T ⟶ D) y = 0 := by
  let := picardCommGrpObj X.hom P R
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let a : X ⊗ T ⟶ J := lift (fst X T) (snd X T ≫ y) ≫ jacobianDifferenceMorphism hX P R
  let v : J ⟶ J ⊗ D := lift (𝟙 J) (1 : J ⟶ D)
  have hm : jacobianDifferenceFamilyMorphism hX P R Q RQ T (1 : T ⟶ D) y = a ≫ v := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [jacobianDifferenceFamilyMorphism, a, v, Category.assoc, lift_fst,
        lift_snd, Category.comp_id, MonObj.comp_one]
  have hz : pullbackClass v.left (jacobianPoincareClass hX P R Q RQ) = 0 :=
    poincareClass_parameter_unit J Q RQ
  change pullbackClass (jacobianDifferenceFamilyMorphism hX P R Q RQ T 1 y).left
    (jacobianPoincareClass hX P R Q RQ) = 0
  rw [hm, Over.comp_left, pullbackClass_comp, hz, pullbackClass_zero]

/-- The whole difference-family section of the ORIGINAL relative Picard
sheaf of X on every test. Representability is not used on those tests. -/
def jacobianDifferenceFamilySection (T : FScheme k) (d : T ⟶ D) (y : T ⟶ X) :
    (fppfPicardSheaf X.hom).obj.obj (op T) :=
  ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
    (jacobianDifferenceFamilyClass hX P R Q RQ T d y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole parameter naturality of the original relative section. -/
theorem jacobianDifferenceFamilySection_naturality {T T' : FScheme k} (f : T' ⟶ T)
    (d : T ⟶ D) (y : T ⟶ X) :
    ((fppfPicardSheaf X.hom).obj.map f.op).hom
        (jacobianDifferenceFamilySection hX P R Q RQ T d y) =
      jacobianDifferenceFamilySection hX P R Q RQ T' (f ≫ d) (f ≫ y) := by
  have H := (NatTrans.naturality_apply
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom) f.op
    (jacobianDifferenceFamilyClass hX P R Q RQ T d y)).symm
  refine H.trans ?_
  change ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T')).hom
      (pullbackClass ((familyScheme X.hom).map f)
        (jacobianDifferenceFamilyClass hX P R Q RQ T d y)) = _
  exact congrArg
    (((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T')).hom)
    (jacobianDifferenceFamilyClass_naturality hX P R Q RQ f d y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original relative section is zero on the actual D-unit family. -/
theorem jacobianDifferenceFamilySection_parameter_one (T : FScheme k) (y : T ⟶ X) :
    jacobianDifferenceFamilySection hX P R Q RQ T (1 : T ⟶ D) y = 0 := by
  change ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
    (jacobianDifferenceFamilyClass hX P R Q RQ T 1 y) = 0
  rw [jacobianDifferenceFamilyClass_parameter_one, map_zero]

variable [IsSeparated Q.obj.hom]

include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descentDualGeometry
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    IsProper (D).hom ∧ GeometricallyIntegral (D).hom := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  have H := isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
    J Q RQ hH1
  let : IsHProjective (D).hom := H.1
  exact ⟨inferInstance, H.2.2.1⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem jacobianDifferenceFamilyClass_changeOrigin_of_geometry
    [IsProper (D).hom] [GeometricallyIntegral (D).hom]
    (T : FScheme k) (d : T ⟶ D) (y z : T ⟶ X) :
    jacobianDifferenceFamilyClass hX P R Q RQ T d z -
        jacobianDifferenceFamilyClass hX P R Q RQ T d y =
      pullbackClass (pullback.snd X.hom T.hom)
        (pullbackClass (lift ((lift z y ≫ jacobianDifferenceMorphism hX P R)⁻¹) d).left
          (jacobianPoincareClass hX P R Q RQ)) := by
  let := picardCommGrpObj X.hom P R
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let U := jacobianPoincareClass hX P R Q RQ
  let a : X ⊗ T ⟶ J := lift (fst X T) (snd X T ≫ y) ≫ jacobianDifferenceMorphism hX P R
  let az : X ⊗ T ⟶ J := lift (fst X T) (snd X T ≫ z) ≫ jacobianDifferenceMorphism hX P R
  let b : T ⟶ J := lift z y ≫ jacobianDifferenceMorphism hX P R
  let t : T ⟶ J := b⁻¹
  let g : X ⊗ T ⟶ J := snd X T ≫ t
  let d' : X ⊗ T ⟶ D := snd X T ≫ d
  have hb : lift (snd X T ≫ z) (snd X T ≫ y) ≫ jacobianDifferenceMorphism hX P R =
      snd X T ≫ b := by
    dsimp only [b]
    rw [CartesianMonoidalCategory.comp_lift_assoc]
  have hc : az = a / (snd X T ≫ b) := by
    have H := jacobianDifferenceMorphism_cocycle hX P R (fst X T)
      (snd X T ≫ y) (snd X T ≫ z)
    change az = a / (lift (snd X T ≫ z) (snd X T ≫ y) ≫
      jacobianDifferenceMorphism hX P R) at H
    rw [hb] at H
    exact H
  have hinv : snd X T ≫ t = (snd X T ≫ b)⁻¹ := by
    change snd X T ≫ b⁻¹ = _
    rw [← one_div b, GrpObj.comp_div, MonObj.comp_one, one_div]
  have hf : az = a * g := by
    calc
      az = a / (snd X T ≫ b) := hc
      _ = a * g := by dsimp only [g]; rw [div_eq_mul_inv, hinv]
  have hz : jacobianDifferenceFamilyMorphism hX P R Q RQ T d z = lift (a * g) d' := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [jacobianDifferenceFamilyMorphism, lift_fst]
      exact hf
    · simp only [jacobianDifferenceFamilyMorphism, lift_snd, d']
  have hy : jacobianDifferenceFamilyMorphism hX P R Q RQ T d y = lift a d' := rfl
  have hbase : lift g d' = snd X T ≫ lift t d := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [g, d', Category.assoc, lift_fst, lift_snd]
  have H := poincareClass_pullback_mul J Q RQ a g d'
  change pullbackClass (lift (a * g) d').left U =
      pullbackClass (lift a d').left U + pullbackClass (lift g d').left U at H
  rw [← hz, ← hy, hbase, Over.comp_left, pullbackClass_comp] at H
  change jacobianDifferenceFamilyClass hX P R Q RQ T d z =
      jacobianDifferenceFamilyClass hX P R Q RQ T d y +
        pullbackClass (pullback.snd X.hom T.hom)
          (pullbackClass (lift ((lift z y ≫ jacobianDifferenceMorphism hX P R)⁻¹) d).left
            (jacobianPoincareClass hX P R Q RQ)) at H
  exact sub_eq_iff_eq_add.mpr (H.trans (add_comm _ _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole original origin-change class law. Its base evaluation factor is
retained explicitly; only the later relative quotient will annihilate it.
Actual dual geometry is derived from the displayed original H1 premise. -/
theorem jacobianDifferenceFamilyClass_changeOrigin
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (T : FScheme k) (d : T ⟶ D) (y z : T ⟶ X) :
    jacobianDifferenceFamilyClass hX P R Q RQ T d z -
        jacobianDifferenceFamilyClass hX P R Q RQ T d y =
      pullbackClass (pullback.snd X.hom T.hom)
        (pullbackClass (lift ((lift z y ≫ jacobianDifferenceMorphism hX P R)⁻¹) d).left
          (jacobianPoincareClass hX P R Q RQ)) := by
  have H := descentDualGeometry hX P R Q RQ hH1
  let : IsProper (D).hom := H.1
  let : GeometricallyIntegral (D).hom := H.2
  exact jacobianDifferenceFamilyClass_changeOrigin_of_geometry hX P R Q RQ T d y z

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem curvePicard_basePullback_zero (T : FScheme k) (c : PicardGroup T.left) :
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
      (pullbackClass (pullback.snd X.hom T.hom) c) = 0 := by
  change ((toFppfPicardSheaf X.hom).app (op T)).hom
    (((quotientProjection X.hom).app (op T)).hom
      (((basePullback X.hom).app (op T)).hom c)) = 0
  rw [quotientProjection_basePullback_apply, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original relative section is independent of the varying origin
on EVERY test, including nonreduced and non-Noetherian overlaps. The
statement applies no representability equivalence to such a test. -/
theorem jacobianDifferenceFamilySection_changeOrigin
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (T : FScheme k) (d : T ⟶ D) (y z : T ⟶ X) :
    jacobianDifferenceFamilySection hX P R Q RQ T d z =
      jacobianDifferenceFamilySection hX P R Q RQ T d y := by
  let q : PicardGroup (pullback X.hom T.hom) →+
      (fppfPicardSheaf X.hom).obj.obj (op T) :=
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
  have H := congrArg q (jacobianDifferenceFamilyClass_changeOrigin hX P R Q RQ hH1 T d y z)
  have hbase := curvePicard_basePullback_zero (X := X) T
    (pullbackClass (lift ((lift z y ≫ jacobianDifferenceMorphism hX P R)⁻¹) d).left
      (jacobianPoincareClass hX P R Q RQ))
  change q (jacobianDifferenceFamilyClass hX P R Q RQ T d z) =
    q (jacobianDifferenceFamilyClass hX P R Q RQ T d y)
  exact sub_eq_zero.mp ((map_sub q _ _).symm.trans (H.trans hbase))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem jacobianDifferenceFamilySection_compatible
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    {T : FScheme k} (a b : T ⟶ D ⊗ X) (hab : a ≫ fst D X = b ≫ fst D X) :
    ((fppfPicardSheaf X.hom).obj.map a.op).hom
        (jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)) =
      ((fppfPicardSheaf X.hom).obj.map b.op).hom
        (jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)) := by
  have ha := jacobianDifferenceFamilySection_naturality hX P R Q RQ a
    (fst D X) (snd D X)
  have hb := jacobianDifferenceFamilySection_naturality hX P R Q RQ b
    (fst D X) (snd D X)
  have horigin := jacobianDifferenceFamilySection_changeOrigin hX P R Q RQ hH1 T
    (a ≫ fst D X) (b ≫ snd D X) (a ≫ snd D X)
  have hdual := congrArg
    (fun d : T ⟶ D => jacobianDifferenceFamilySection hX P R Q RQ T d (b ≫ snd D X)) hab
  exact ha.trans (horigin.trans (hdual.trans hb.symm))

omit [IsSeparated P.obj.hom] [IsSeparated Q.obj.hom] in
include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descentParameters_locallyNoetherian :
    IsLocallyNoetherian (D).left ∧ IsLocallyNoetherian (D ⊗ X).left ∧
      IsLocallyNoetherian (D ⊗ (X ⊗ X)).left := by
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj (J).hom Q RQ
  let := hX.smooth
  let := hX.proper
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian (X ⊗ X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd X.hom X.hom)
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian (D).hom,
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (D).hom X.hom),
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (D).hom (X ⊗ X).hom)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole compatible family has a unique section over the actual dual
parameter, by the fppf sheaf condition on the original Picard sheaf. -/
theorem existsUnique_canonicalAbelPicardSection
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    ∃! s : (fppfPicardSheaf X.hom).obj.obj (op D),
      ((fppfPicardSheaf X.hom).obj.map (fst D X).op).hom s =
        jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X) := by
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj (J).hom Q RQ
  let := hX.smooth
  let := hX.proper
  let : GeometricallyIntegral X.hom := hX.isGeometricallyIntegral
  have Hnoe := descentParameters_locallyNoetherian hX P R Q RQ
  let TD : LocallyNoetherianOver (Spec (.of k)) := ⟨D, Hnoe.1⟩
  let TZ : LocallyNoetherianOver (Spec (.of k)) := ⟨D ⊗ X, Hnoe.2.1⟩
  let q : TZ ⟶ TD := ObjectProperty.homMk (fst D X)
  have : Flat q.hom.left := by
    change Flat (pullback.fst (D).hom X.hom)
    infer_instance
  have : Surjective q.hom.left := by
    change Surjective (pullback.fst (D).hom X.hom)
    infer_instance
  have : LocallyOfFinitePresentation q.hom.left := by
    change LocallyOfFinitePresentation (pullback.fst (D).hom X.hom)
    infer_instance
  let F : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1) :=
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  have hF : Presieve.IsSheaf (Scheme.fppfTopology.over (Spec (.of k))) F :=
    isSheaf_fppfPicardSheaf_forget X.hom
  let z : F.obj (op TZ.obj) :=
    jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)
  have hc : ∀ ⦃T : LocallyNoetherianOver (Spec (.of k))⦄ (a b : T ⟶ TZ),
      a ≫ q = b ≫ q → F.map a.hom.op z = F.map b.hom.op z := by
    intro T a b hab
    have hd : a.hom ≫ fst D X = b.hom ≫ fst D X :=
      congrArg (fun v : T ⟶ TD => v.hom) hab
    exact jacobianDifferenceFamilySection_compatible hX P R Q RQ hH1 a.hom b.hom hd
  exact Scheme.existsUnique_map_eq_of_fppfQuotient hF q z hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical section on the ORIGINAL relative Picard sheaf of X,
amalgamated along the actual fppf cover D times X over D. Its construction
chooses no rational origin on X and uses the original H1 premise only to
prove the whole compatibility law. -/
def canonicalAbelPicardSection
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    (fppfPicardSheaf X.hom).obj.obj (op D) := by
  classical
  have H : ∃! s : (fppfPicardSheaf X.hom).obj.obj (op D),
      ((fppfPicardSheaf X.hom).obj.map (fst D X).op).hom s =
        jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X) := by
    exact existsUnique_canonicalAbelPicardSection hX P R Q RQ hH1
  exact H.exists.choose

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual fppf amalgamation restricts to the original whole family. -/
theorem canonicalAbelPicardSection_pullback
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    ((fppfPicardSheaf X.hom).obj.map (fst D X).op).hom
        (canonicalAbelPicardSection hX P R Q RQ hH1) =
      jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X) := by
  exact (existsUnique_canonicalAbelPicardSection hX P R Q RQ hH1).exists.choose_spec

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Uniqueness of the section uses actual sheaf amalgamation, not a
comparison only on algebraically closed field values. -/
theorem canonicalAbelPicardSection_unique
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (s : (fppfPicardSheaf X.hom).obj.obj (op D))
    (hs : ((fppfPicardSheaf X.hom).obj.map (fst D X).op).hom s =
      jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)) :
    s = canonicalAbelPicardSection hX P R Q RQ hH1 := by
  exact (existsUnique_canonicalAbelPicardSection hX P R Q RQ hH1).unique hs
    (canonicalAbelPicardSection_pullback hX P R Q RQ hH1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On every test admitting a curve-valued map, the canonical section is
represented by the original difference family with that variable origin. -/
theorem canonicalAbelPicardSection_map
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (T : FScheme k) (d : T ⟶ D) (y : T ⟶ X) :
    ((fppfPicardSheaf X.hom).obj.map d.op).hom
        (canonicalAbelPicardSection hX P R Q RQ hH1) =
      jacobianDifferenceFamilySection hX P R Q RQ T d y := by
  let F : (FScheme k)ᵒᵖ ⥤ Type (u + 1) :=
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  change F.map d.op (canonicalAbelPicardSection hX P R Q RQ hH1) = _
  calc
    _ = F.map (lift d y).op (F.map (fst D X).op
        (canonicalAbelPicardSection hX P R Q RQ hH1)) := by
      rw [← Functor.map_comp_apply, ← op_comp, lift_fst]
    _ = F.map (lift d y).op
        (jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)) :=
      congrArg (F.map (lift d y).op)
        (canonicalAbelPicardSection_pullback hX P R Q RQ hH1)
    _ = _ := by
      change ((fppfPicardSheaf X.hom).obj.map (lift d y).op).hom
        (jacobianDifferenceFamilySection hX P R Q RQ (D ⊗ X) (fst D X) (snd D X)) = _
      simpa only [lift_fst, lift_snd] using
        jacobianDifferenceFamilySection_naturality hX P R Q RQ (lift d y)
          (fst D X) (snd D X)

omit [IsSeparated P.obj.hom] [IsSeparated Q.obj.hom] in
private theorem curvePicard_fppfRestriction_injective {T Z : FScheme k} (q : Z ⟶ T)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Function.Injective ((fppfPicardSheaf X.hom).obj.map q.op).hom := by
  let F : (FScheme k)ᵒᵖ ⥤ Type (u + 1) :=
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  have hF : Presieve.IsSheaf (Scheme.fppfTopology.over (Spec (.of k))) F :=
    isSheaf_fppfPicardSheaf_forget X.hom
  have hcov := Scheme.ofArrows_mem_fppfTopology_over
    (fun _ : PUnit.{1} => Z) (fun _ => q) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun t => ⟨PUnit.unit, q.left.surjective t⟩)
  intro a b hab
  apply (hF.isSheafFor _ hcov).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact hab

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original parameter-unit law and fppf sheaf separatedness prove
that the canonical section is zero at the dual unit, without a curve origin. -/
theorem canonicalAbelPicardSection_unit
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    ((fppfPicardSheaf X.hom).obj.map η[D].op).hom
        (canonicalAbelPicardSection hX P R Q RQ hH1) = 0 := by
  let := hX.smooth
  let := hX.proper
  let : GeometricallyIntegral X.hom := hX.isGeometricallyIntegral
  have : Flat (toUnit X).left := by change Flat X.hom; infer_instance
  have : Surjective (toUnit X).left := by change Surjective X.hom; infer_instance
  have : LocallyOfFinitePresentation (toUnit X).left := by
    change LocallyOfFinitePresentation X.hom
    infer_instance
  apply curvePicard_fppfRestriction_injective (X := X) (toUnit X)
  let F : (FScheme k)ᵒᵖ ⥤ Type (u + 1) :=
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  change F.map (toUnit X).op (F.map η[D].op
    (canonicalAbelPicardSection hX P R Q RQ hH1)) = F.map (toUnit X).op 0
  rw [← Functor.map_comp_apply, ← op_comp]
  change F.map (1 : X ⟶ D).op (canonicalAbelPicardSection hX P R Q RQ hH1) = _
  exact (canonicalAbelPicardSection_map hX P R Q RQ hH1 X 1 (𝟙 X)).trans
    ((jacobianDifferenceFamilySection_parameter_one hX P R Q RQ X (𝟙 X)).trans
      (map_zero ((fppfPicardSheaf X.hom).obj.map (toUnit X).op).hom).symm)

/-- The canonical section classified by the ORIGINAL Picard representative.
Only the actual locally Noetherian dual parameter is used by R. -/
def canonicalAbelPicardMorphism
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) : D ⟶ P.obj := by
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj (J).hom Q RQ
  let TD : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨D, LocallyOfFiniteType.isLocallyNoetherian (D).hom⟩
  exact (R.homEquiv.symm
    (canonicalAbelPicardSection hX P R Q RQ hH1) : TD ⟶ P).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original represented class equation on every locally Noetherian test. -/
theorem homEquiv_comp_canonicalAbelPicardMorphism
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ D) :
    R.homEquiv (ObjectProperty.homMk
        (t ≫ canonicalAbelPicardMorphism hX P R Q RQ hH1) : T ⟶ P) =
      ((fppfPicardSheaf X.hom).obj.map t.op).hom
        (canonicalAbelPicardSection hX P R Q RQ hH1) := by
  let TD : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨D, (descentParameters_locallyNoetherian hX P R Q RQ).1⟩
  let v : TD ⟶ P := R.homEquiv.symm (canonicalAbelPicardSection hX P R Q RQ hH1)
  change R.homEquiv ((ObjectProperty.homMk t : T ⟶ TD) ≫ v) = _
  exact (R.homEquiv_comp (ObjectProperty.homMk t : T ⟶ TD) v).trans
    (congrArg ((fppfPicardSheaf X.hom).obj.map t.op).hom
      (R.homEquiv.apply_symm_apply _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual classifying morphism preserves the original unit. -/
theorem canonicalAbelPicardMorphism_pointed
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    η[D] ≫ canonicalAbelPicardMorphism hX P R Q RQ hH1 = η[P.obj] := by
  let := picardCommGrpObj X.hom P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨𝟙_ _, inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))⟩
  have H : (ObjectProperty.homMk
      (η[D] ≫ canonicalAbelPicardMorphism hX P R Q RQ hH1) : T ⟶ P) =
      ObjectProperty.homMk η[P.obj] := by
    apply R.homEquiv.injective
    rw [homEquiv_comp_canonicalAbelPicardMorphism, canonicalAbelPicardSection_unit]
    symm
    simpa only [MonObj.one_eq_one] using picard_homEquiv_one X.hom P R T
  exact congrArg (fun v : T ⟶ P => v.hom) H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pointed original classifier has image in the original open
identity component; no replacement Picard realization is chosen. -/
theorem canonicalAbelPicardMorphism_range
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    Set.range (canonicalAbelPicardMorphism hX P R Q RQ hH1).left ⊆
      identityComponent P.obj := by
  let := picardCommGrpObj X.hom P R
  exact range_subset_identityComponent_of_section P.obj _ η[D]
    (canonicalAbelPicardMorphism_pointed hX P R Q RQ hH1)

/-- The canonical point-free Abel dual map into the SAME original Jacobian. -/
def canonicalAbelDualMorphism
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) : D ⟶ J :=
  letI := picardCommGrpObj X.hom P R
  liftIdentityComponent P.obj (canonicalAbelPicardMorphism hX P R Q RQ hH1)
    (canonicalAbelPicardMorphism_range hX P R Q RQ hH1)

@[reassoc (attr := simp)]
theorem canonicalAbelDualMorphism_comp_inclusion
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    canonicalAbelDualMorphism hX P R Q RQ hH1 ≫ picardIdentityComponentι X.hom P R =
      canonicalAbelPicardMorphism hX P R Q RQ hH1 := by
  let := picardCommGrpObj X.hom P R
  exact liftIdentityComponent_ι P.obj _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pointedness holds as an equation of the original whole morphisms. -/
theorem canonicalAbelDualMorphism_pointed
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    η[D] ≫ canonicalAbelDualMorphism hX P R Q RQ hH1 = η[J] := by
  let := picardCommGrpObj X.hom P R
  rw [← cancel_mono (picardIdentityComponentι X.hom P R), Category.assoc,
    canonicalAbelDualMorphism_comp_inclusion, canonicalAbelPicardMorphism_pointed,
    IsMonHom.one_hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper-source rigidity proves the original canonical map is a group map. -/
theorem isMonHom_canonicalAbelDualMorphism
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    IsMonHom (canonicalAbelDualMorphism hX P R Q RQ hH1) := by
  let := picardCommGrpObj X.hom P R
  let := picardCommGrpObj (J).hom Q RQ
  have H := descentDualGeometry hX P R Q RQ hH1
  let : IsProper (D).hom := H.1
  let : GeometricallyIntegral (D).hom := H.2
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : LocallyOfFiniteType (J).hom := inferInstance
  exact Group.PointedMorphism.isMonHom_of_geometricallyIntegral_of_isSeparated D J _
    (canonicalAbelDualMorphism_pointed hX P R Q RQ hH1)

/-- The same canonical map in the existing category of group schemes. -/
def canonicalAbelDualGroupHom
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) : Grp.mk D ⟶ Grp.mk J :=
  letI := isMonHom_canonicalAbelDualMorphism hX P R Q RQ hH1
  Grp.ofHom (canonicalAbelDualMorphism hX P R Q RQ hH1)

omit [IsSeparated P.obj.hom] [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem positiveCurveMorphism_eq_originalBased
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    letI := picardCommGrpObj X.hom P R
    positiveCurveMorphism hX P R =
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
  have H := congrArg (fun v : parameter X.hom 1 ⟶ P.obj => singleParameterMorphism X ≫ v)
    (positiveAbelMorphism_eq_based_mul_constant hX o ho P R 1)
  change singleParameterMorphism X ≫ (positiveAbelMorphism X P R 1).hom = _
  refine H.trans ?_
  rw [MonObj.comp_mul]
  exact congrArg₂ (fun v w : X ⟶ P.obj => v * w)
    (jacobianCurveMorphism_comp_inclusion hX o ho P R).symm hc

omit [IsSeparated P.obj.hom] [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Choosing one origin identifies the point-free difference with the
whole difference of the original based Abel morphisms, on arbitrary tests. -/
theorem jacobianDifferenceMorphism_eq_basedDifference
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    {T : FScheme k} (x y : T ⟶ X) :
    lift x y ≫ jacobianDifferenceMorphism hX P R =
      (x ≫ jacobianCurveMorphism hX o ho P R) /
        (y ≫ jacobianCurveMorphism hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let f := jacobianCurveMorphism hX o ho P R
  let j : J ⟶ P.obj := identityComponentι P.obj
  let c := picardPoint P R (classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
  have hp : positiveCurveMorphism hX P R = (f ≫ j) * (toUnit X ≫ c) :=
    positiveCurveMorphism_eq_originalBased hX P R o ho
  apply (cancel_mono (identityComponentι P.obj)).mp
  simp only [GrpObj.div_comp, Category.assoc, jacobianDifferenceMorphism_comp_inclusion]
  simp only [curveDifferencePicardMorphism, GrpObj.comp_div, ← Category.assoc,
    lift_fst, lift_snd]
  rw [hp, MonObj.comp_mul, MonObj.comp_mul, comp_toUnit_assoc, comp_toUnit_assoc]
  simp only [div_eq_mul_inv, mul_inv_rev, ← _root_.mul_assoc, mul_inv_cancel_right]
  simp only [f, j, Category.assoc]

omit [IsSeparated P.obj.hom] [IsSeparated Q.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem jacobianDifferenceFamilyMorphism_based
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    jacobianDifferenceFamilyMorphism hX P R Q RQ D (𝟙 D)
        (toUnit D ≫ (Over.homMk o ho : 𝟙_ (FScheme k) ⟶ X)) =
      jacobianCurveMorphism hX o ho P R ⊗ₘ 𝟙 D := by
  let f := jacobianCurveMorphism hX o ho P R
  let u : 𝟙_ (FScheme k) ⟶ X := Over.homMk o ho
  have hu : u ≫ f = η[J] := jacobianCurveMorphism_pointed hX o ho P R
  apply CartesianMonoidalCategory.hom_ext
  · simp only [jacobianDifferenceFamilyMorphism, lift_fst, tensorHom_fst]
    rw [jacobianDifferenceMorphism_eq_basedDifference hX P R o ho]
    have hy : (snd X D ≫ (toUnit D ≫ u)) ≫ f = 1 := by
      rw [Category.assoc, Category.assoc, hu, comp_toUnit_assoc]
      rfl
    change (fst X D ≫ f) / ((snd X D ≫ (toUnit D ≫ u)) ≫ f) = fst X D ≫ f
    rw [hy, div_one]
  · simp only [jacobianDifferenceFamilyMorphism, lift_snd, Category.comp_id, tensorHom_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whenever the curve has one origin, the canonical point-free map is
exactly pullback along that SAME original Abel map. The construction itself
selects no origin, and the identification is a whole morphism equation. -/
theorem canonicalAbelDualMorphism_eq_originalPullback
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    canonicalAbelDualMorphism hX P R Q RQ hH1 =
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let TD : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨D, LocallyOfFiniteType.isLocallyNoetherian (D).hom⟩
  let f := jacobianCurveMorphism hX o ho P R
  let u : 𝟙_ (FScheme k) ⟶ X := Over.homMk o ho
  let a := jacobianPoincareClass hX P R Q RQ
  let qJ : PicardGroup (pullback (J).hom (D).hom) →+
      (fppfPicardSheaf (J).hom).obj.obj (op D) :=
    ((quotientProjection (J).hom ≫ toFppfPicardSheaf (J).hom).app (op D)).hom
  have ha : qJ a = RQ.homEquiv
      (ObjectProperty.homMk (picardIdentityComponentι (J).hom Q RQ) : TD ⟶ Q) := by
    have H := poincarePullback_fppfClass J Q RQ (T := TD) (𝟙 D)
    change qJ (classOf (pullback (J).hom (D).hom)
      (poincarePullback J Q RQ (𝟙 D)).bundle) =
        RQ.homEquiv (ObjectProperty.homMk
          (𝟙 D ≫ picardIdentityComponentι (J).hom Q RQ) : TD ⟶ Q) at H
    have he : classOf (pullback (J).hom (D).hom) (poincarePullback J Q RQ (𝟙 D)).bundle = a :=
      Quotient.sound ⟨(poincarePullbackIdIso J Q RQ).iso⟩
    rw [he, Category.id_comp] at H
    exact H
  have hm : (jacobianDifferenceFamilyMorphism hX P R Q RQ D (𝟙 D)
      (toUnit D ≫ u)).left = familyMapOfHom f D := by
    rw [jacobianDifferenceFamilyMorphism_based hX P R Q RQ o ho,
      familyMapOfHom_eq_tensorHom]
  have hs := canonicalAbelPicardSection_map hX P R Q RQ hH1 D (𝟙 D) (toUnit D ≫ u)
  rw [op_id, CategoryTheory.Functor.map_id] at hs
  change canonicalAbelPicardSection hX P R Q RQ hH1 = _ at hs
  have hmap := homEquiv_comp_canonicalAbelPicardMorphism hX P R Q RQ hH1
    (T := TD) (𝟙 D)
  rw [Category.id_comp, op_id, CategoryTheory.Functor.map_id] at hmap
  change R.homEquiv (ObjectProperty.homMk
    (canonicalAbelPicardMorphism hX P R Q RQ hH1) : TD ⟶ P) =
      canonicalAbelPicardSection hX P R Q RQ hH1 at hmap
  have hp := homEquiv_comp_picardIdentityComponentPullback P R Q RQ f
    (T := TD) (𝟙 D)
  have hfull : (ObjectProperty.homMk
      (canonicalAbelPicardMorphism hX P R Q RQ hH1) : TD ⟶ P) =
      ObjectProperty.homMk
        (picardIdentityComponentPullback P R Q RQ f ≫ picardIdentityComponentι X.hom P R) := by
    apply R.homEquiv.injective
    calc
      _ = canonicalAbelPicardSection hX P R Q RQ hH1 := hmap
      _ = jacobianDifferenceFamilySection hX P R Q RQ D (𝟙 D) (toUnit D ≫ u) := hs
      _ = ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op D)).hom
          (pullbackClass (familyMapOfHom f D) a) := by
        simp only [jacobianDifferenceFamilySection, jacobianDifferenceFamilyClass, hm, a]
      _ = ((fppfPicardPullback f).hom.app (op D)).hom (qJ a) :=
        fppfPicardPullback_class f D a
      _ = _ := by rw [ha]; exact hp.symm
  apply (cancel_mono (picardIdentityComponentι X.hom P R)).mp
  rw [canonicalAbelDualMorphism_comp_inclusion]
  exact congrArg (fun v : TD ⟶ P => v.hom) hfull

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over an algebraically closed field of positive genus, the same
canonical map is an isomorphism by the accepted original theta equation.
The coherent H1 bound remains the original explicit premise. -/
theorem isIso_canonicalAbelDualMorphism_of_positiveGenus [IsAlgClosed k]
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (hg : 0 < coherentGenus k X) :
    IsIso (canonicalAbelDualMorphism hX P R Q RQ hH1) := by
  let := hX.smooth
  let := hX.proper
  let : GeometricallyIntegral X.hom := hX.isGeometricallyIntegral
  have : Surjective X.hom := inferInstance
  obtain ⟨o, ho⟩ := Scheme.Hom.exists_lift_spec_of_isAlgClosed X.hom k (𝟙 _)
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let e := thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1
  have he : e.inv = canonicalAbelDualMorphism hX P R Q RQ hH1 ≫ ι[J] := by
    rw [canonicalAbelDualMorphism_eq_originalPullback hX P R Q RQ hH1 o ho]
    exact thetaPrincipalIsoOfStructureH1Le_inv hX o ho P R Q RQ hg hH1
  have hm : canonicalAbelDualMorphism hX P R Q RQ hH1 = e.inv ≫ ι[J] := by
    rw [he, Category.assoc, GrpObj.inv_comp_inv, Category.comp_id]
  rw [hm]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In genus zero the original Jacobian and its original dual are the
actual unit schemes. This branch uses no theta locus in negative degree. -/
theorem isIso_canonicalAbelDualMorphism_of_genusZero
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J]))
    (hg : coherentGenus k X = 0) :
    IsIso (canonicalAbelDualMorphism hX P R Q RQ hH1) := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  have H := isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
    J Q RQ hH1
  let : Smooth (D).hom := H.2.1
  let : GeometricallyIntegral (D).hom := H.2.2.1
  let : IsIntegral (D).left := GeometricallyIntegral.isIntegral_of_subsingleton (D).hom
  have hdJ : SmoothOfRelativeDimension 0 (J).hom := by
    simpa only [hg] using smoothOfRelativeDimension_identityComponentOver hX P R
  let := hdJ
  have hcJ : Module.finrank k (Cotangent.Space η[J]) = 0 := Cotangent.finrank η[J] 0
  have hcD : Module.finrank k (Cotangent.Space η[D]) = 0 := by
    have hi := identityComponentCotangent_le_of_structureH1_le J Q RQ hH1
    exact Nat.eq_zero_of_le_zero (hi.trans hcJ.le)
  have hdD : SmoothOfRelativeDimension 0 (D).hom := by
    simpa only [hcD] using
      Group.smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected D
  let : Etale (D).hom := (Etale.iff_smoothOfRelativeDimension_zero _).mpr hdD
  let : IsIso (D).hom :=
    (isoSpecOfEtaleOfPreconnected (D).hom η[D].left (Over.w η[D])).isIso_hom
  let : IsIso (J).hom := isIso_identityComponentOver_hom_of_genus_zero hX P R hg
  have : IsIso ((Over.forget (Spec (.of k))).map (toUnit D)) := by
    change IsIso (D).hom
    infer_instance
  have : IsIso (toUnit D) := isIso_of_reflects_iso _ (Over.forget (Spec (.of k)))
  have : IsIso ((Over.forget (Spec (.of k))).map (toUnit J)) := by
    change IsIso (J).hom
    infer_instance
  have : IsIso (toUnit J) := isIso_of_reflects_iso _ (Over.forget (Spec (.of k)))
  have : IsIso (canonicalAbelDualMorphism hX P R Q RQ hH1 ≫ toUnit J) := by
    rw [comp_toUnit]
    infer_instance
  exact IsIso.of_isIso_comp_right (canonicalAbelDualMorphism hX P R Q RQ hH1) (toUnit J)

/-- Every genus over an algebraically closed field is covered by the
original positive-theta branch or the actual genus-zero unit branch. -/
theorem isIso_canonicalAbelDualMorphism_of_isAlgClosed [IsAlgClosed k]
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    IsIso (canonicalAbelDualMorphism hX P R Q RQ hH1) := by
  by_cases hg : coherentGenus k X = 0
  · exact isIso_canonicalAbelDualMorphism_of_genusZero hX P R Q RQ hH1 hg
  · exact isIso_canonicalAbelDualMorphism_of_positiveGenus hX P R Q RQ hH1
      (Nat.pos_of_ne_zero hg)

end AlgebraicGeometry.Scheme.OverField.Curve
