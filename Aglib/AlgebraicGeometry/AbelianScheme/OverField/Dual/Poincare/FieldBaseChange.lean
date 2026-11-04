/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Homogeneity
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback

/-! The original Poincare fppf class under the original scalar extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Cohomology Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

private theorem poincareClass_universalFppfClass
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
    (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    {T : FScheme k} (t : T ⟶ picardIdentityComponent A.hom Q RQ) :
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op T)).hom
        (pullbackClass ((familyScheme A.hom).map t) (poincareClass A Q RQ)) =
      ((fppfPicardSheaf A.hom).obj.map
        (t ≫ picardIdentityComponentι A.hom Q RQ).op).hom (RQ.homEquiv (𝟙 Q)) := by
  let D := picardIdentityComponent A.hom Q RQ
  let TD : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨D, LocallyOfFiniteType.isLocallyNoetherian D.hom⟩
  let q : PicardGroup (pullback A.hom D.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op D) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op D)).hom
  have hi : q (poincareClass A Q RQ) =
      RQ.homEquiv (ObjectProperty.homMk (picardIdentityComponentι A.hom Q RQ) : TD ⟶ Q) := by
    have H := poincarePullback_fppfClass A Q RQ (T := TD) (𝟙 D)
    change q (classOf (pullback A.hom D.hom) (poincarePullback A Q RQ (𝟙 D)).bundle) =
      RQ.homEquiv (ObjectProperty.homMk
        (𝟙 D ≫ picardIdentityComponentι A.hom Q RQ) : TD ⟶ Q) at H
    have hc : classOf (pullback A.hom D.hom) (poincarePullback A Q RQ (𝟙 D)).bundle =
        poincareClass A Q RQ := Quotient.sound ⟨(poincarePullbackIdIso A Q RQ).iso⟩
    rw [hc, Category.id_comp] at H
    exact H
  have hu : q (poincareClass A Q RQ) =
      ((fppfPicardSheaf A.hom).obj.map (picardIdentityComponentι A.hom Q RQ).op).hom
        (RQ.homEquiv (𝟙 Q)) := hi.trans
      (RQ.homEquiv_eq (ObjectProperty.homMk
        (picardIdentityComponentι A.hom Q RQ) : TD ⟶ Q))
  have H := (NatTrans.naturality_apply
    (quotientProjection A.hom ≫ toFppfPicardSheaf A.hom) t.op (poincareClass A Q RQ)).symm
  change ((fppfPicardSheaf A.hom).obj.map t.op).hom (q (poincareClass A Q RQ)) =
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op T)).hom
      (pullbackClass ((familyScheme A.hom).map t) (poincareClass A Q RQ)) at H
  rw [hu] at H
  rw [op_comp, CategoryTheory.Functor.map_comp]
  exact H.symm

/-- The original family class and original fppf base-change isomorphism commute. -/
theorem fppfPicardClass_fieldBaseChange
    (A : FScheme k) (K : Type u) [Field K] [Algebra k K]
    (T : FScheme K)
    (c : PicardGroup (pullback A.hom
      (T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    ((fppfPicardSheafBaseChangeIso A.hom b).inv.app (op T)).hom
        (((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app
          (op ((Over.map b).obj T))).hom c) =
      ((quotientProjection (pullback.snd A.hom b) ≫
        toFppfPicardSheaf (pullback.snd A.hom b)).app (op T)).hom
          (pullbackClass (familyBaseChangeIso A.hom b T).hom c) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e := fppfPicardSheafBaseChangeIso A.hom b
  let q0 : PicardGroup (pullback A.hom (T.hom ≫ b)) →+
      (fppfPicardSheaf A.hom).obj.obj (op ((Over.map b).obj T)) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app
      (op ((Over.map b).obj T))).hom
  let q1 : PicardGroup (pullback (pullback.snd A.hom b) T.hom) →+
      (fppfPicardSheaf (pullback.snd A.hom b)).obj.obj (op T) :=
    ((quotientProjection (pullback.snd A.hom b) ≫
      toFppfPicardSheaf (pullback.snd A.hom b)).app (op T)).hom
  apply (e.app (op T)).addCommGroupIsoToAddEquiv.injective
  have hi := fppfPicardSheafBaseChangeIso_hom_app_inv_app_apply A.hom b (q0 c)
  have H := fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk A.hom b (op T)
    (pullbackClass (familyBaseChangeIso A.hom b T).hom c)
  change ((fppfPicardSheafBaseChangeIso A.hom b).hom.app (op T)).hom
      (q1 (pullbackClass (familyBaseChangeIso A.hom b T).hom c)) =
    q0 (pullbackClass (familyBaseChangeIso A.hom b T).inv
      (pullbackClass (familyBaseChangeIso A.hom b T).hom c)) at H
  rw [← pullbackClass_comp, Iso.inv_hom_id, pullbackClass_id] at H
  have hfinal := hi.trans H.symm
  change ((fppfPicardSheafBaseChangeIso A.hom b).hom.app (op T)).hom
      (((fppfPicardSheafBaseChangeIso A.hom b).inv.app (op T)).hom (q0 c)) =
    ((fppfPicardSheafBaseChangeIso A.hom b).hom.app (op T)).hom
      (q1 (pullbackClass (familyBaseChangeIso A.hom b T).hom c))
  exact hfinal

/-- The original Poincare class classifies the original point on a represented test. -/
theorem poincareClass_representedFppfClass
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
    (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    {T : LocallyNoetherianOver (Spec (.of k))}
    (t : T.obj ⟶ picardIdentityComponent A.hom Q RQ) :
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op T.obj)).hom
        (pullbackClass ((familyScheme A.hom).map t) (poincareClass A Q RQ)) =
      RQ.homEquiv (ObjectProperty.homMk
        (t ≫ picardIdentityComponentι A.hom Q RQ) : T ⟶ Q) :=
  (poincareClass_universalFppfClass A Q RQ t).trans
    (RQ.homEquiv_eq (ObjectProperty.homMk
      (t ≫ picardIdentityComponentι A.hom Q RQ) : T ⟶ Q)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original Poincare fppf class commutes with the original
identity-component comparison after field extension. -/
theorem poincareClass_fieldBaseChange
    (A : FScheme k) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
    (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
    (K : Type u) [Field K] [Algebra k K]
    (T : LocallyNoetherianOver (Spec (.of K)))
    (t : T.obj ⟶ fieldBaseChange K (picardIdentityComponent A.hom Q RQ)) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let A' := fieldBaseChange K A
    let Q' := LocallyNoetherianOver.baseChange b Q
    let RQ' := baseChangeRepresentableBy A.hom b Q RQ
    let e := Over.isoMk (picardIdentityComponentBaseChangeIso A.hom Q RQ K)
      (picardIdentityComponentBaseChangeIso_hom_comp A.hom Q RQ K)
    let d := ((Over.mapPullbackAdj b).homEquiv T.obj
      (picardIdentityComponent A.hom Q RQ)).symm t
    letI : GrpObj A' := by
      change GrpObj ((Over.pullback b).obj A)
      exact Functor.grpObjObj (F := Over.pullback b) (G := A)
    letI : IsProper A'.hom := by
      change IsProper (pullback.snd A.hom b)
      infer_instance
    letI : GeometricallyIntegral A'.hom := by
      change GeometricallyIntegral (pullback.snd A.hom b)
      infer_instance
    ((fppfPicardSheafBaseChangeIso A.hom b).inv.app (op T.obj)).hom
      (((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app
        (op ((Over.map b).obj T.obj))).hom
          (pullbackClass ((familyScheme A.hom).map d) (poincareClass A Q RQ))) =
    ((quotientProjection A'.hom ≫ toFppfPicardSheaf A'.hom).app (op T.obj)).hom
      (pullbackClass ((familyScheme A'.hom).map (t ≫ e.hom)) (poincareClass A' Q' RQ')) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let A' := fieldBaseChange K A
  let Q' := LocallyNoetherianOver.baseChange b Q
  let RQ' := baseChangeRepresentableBy A.hom b Q RQ
  let D := picardIdentityComponent A.hom Q RQ
  let e : fieldBaseChange K D ≅ picardIdentityComponent A'.hom Q' RQ' :=
    Over.isoMk (picardIdentityComponentBaseChangeIso A.hom Q RQ K)
      (picardIdentityComponentBaseChangeIso_hom_comp A.hom Q RQ K)
  let d : ((LocallyNoetherianOver.map b).obj T).obj ⟶ D :=
    ((Over.mapPullbackAdj b).homEquiv T.obj D).symm t
  let : GrpObj A' := by
    change GrpObj ((Over.pullback b).obj A)
    exact Functor.grpObjObj (F := Over.pullback b) (G := A)
  let : IsProper A'.hom := by change IsProper (pullback.snd A.hom b); infer_instance
  let : GeometricallyIntegral A'.hom := by
    change GeometricallyIntegral (pullback.snd A.hom b)
    infer_instance
  have ht : ((Over.mapPullbackAdj b).homEquiv T.obj Q.obj).symm
      ((t ≫ e.hom) ≫ picardIdentityComponentι A'.hom Q' RQ') =
      d ≫ picardIdentityComponentι A.hom Q RQ := by
    have hc : e.hom ≫ picardIdentityComponentι A'.hom Q' RQ' =
        (Over.pullback b).map (picardIdentityComponentι A.hom Q RQ) := by
      apply Over.OverMorphism.ext
      exact picardIdentityComponentBaseChangeIso_hom_ι Q RQ K
    rw [Category.assoc, hc]
    exact (Over.mapPullbackAdj b).homEquiv_naturality_right_symm t _
  have H := baseChangeRepresentableBy_homEquiv A.hom b Q RQ (T := T)
    (ObjectProperty.homMk
      ((t ≫ e.hom) ≫ picardIdentityComponentι A'.hom Q' RQ') : T ⟶ Q')
  change RQ'.homEquiv (ObjectProperty.homMk
      ((t ≫ e.hom) ≫ picardIdentityComponentι A'.hom Q' RQ') : T ⟶ Q') =
    ((fppfPicardSheafBaseChangeIso A.hom b).inv.app (op T.obj)).hom
      (RQ.homEquiv (ObjectProperty.homMk
        (((Over.mapPullbackAdj b).homEquiv T.obj Q.obj).symm
          ((t ≫ e.hom) ≫ picardIdentityComponentι A'.hom Q' RQ')) :
            (LocallyNoetherianOver.map b).obj T ⟶ Q)) at H
  rw [ht] at H
  have h0 := poincareClass_representedFppfClass A Q RQ
    (T := (LocallyNoetherianOver.map b).obj T) d
  have h1 := poincareClass_representedFppfClass A' Q' RQ' (T := T) (t ≫ e.hom)
  exact (congrArg ((fppfPicardSheafBaseChangeIso A.hom b).inv.app (op T.obj)).hom h0).trans
    (H.symm.trans h1.symm)

end AlgebraicGeometry.Scheme.RelativePicard
