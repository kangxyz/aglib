/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback
public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelCurve

/-!
# Original represented pullback, universal-family coherence and the actual Abel consumer

The raw map needs no origins or source geometry. Base change uses a merely
locally Noetherian new base, which may be nonreduced. Universal-pair coherence
retains genuine source geometry and pointedness. The original Abel map is an
input to the generic Pic0 operation without any source-J projectivity or dual
geometry assumption.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.Group Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

section General

variable {S : Scheme.{u}} {X Y : Over S}
  (PX : LocallyNoetherianOver S)
  (RX : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PX)
  (PY : LocallyNoetherianOver S)
  (RY : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf Y.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PY)

example (f : X ⟶ Y) {T : Over S} (t : T ⟶ PY.obj) :
    ((fppfPicardSheaf X.hom).obj.map (t ≫ picardPullback PX RX PY RY f).op).hom
        (RX.homEquiv (𝟙 PX)) =
      ((fppfPicardPullback f).hom.app (op T)).hom
        (((fppfPicardSheaf Y.hom).obj.map t.op).hom (RY.homEquiv (𝟙 PY))) :=
  universalFppfClass_picardPullback PX RX PY RY f t

example {S' : Scheme.{u}} [IsLocallyNoetherian S']
    [LocallyOfFiniteType PX.obj.hom] [LocallyOfFiniteType PY.obj.hom]
    (f : X ⟶ Y) (b : S' ⟶ S) :
    picardPullback (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
        (LocallyNoetherianOver.baseChange b PX) (baseChangeRepresentableBy X.hom b PX RX)
        (LocallyNoetherianOver.baseChange b PY) (baseChangeRepresentableBy Y.hom b PY RY)
        ((Over.pullback b).map f) =
      (Over.pullback b).map (picardPullback PX RX PY RY f) :=
  picardPullback_baseChange PX RX PY RY f b

example [IsLocallyNoetherian S]
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [Flat Y.hom] [GeometricallyIntegral Y.hom]
    (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y)
    (f : X ⟶ Y) (hf : oX ≫ f = oY) {T : Over S} (t : T ⟶ PY.obj) :
    Nonempty (RigidifiedPair.Iso
      (RigidifiedPair.map (t ≫ picardPullback PX RX PY RY f)
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))
      (RigidifiedPair.sourcePullback oX oY f hf (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)))) :=
  ⟨picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf t⟩

end General

section ActualAbelMap

example {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (PC : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PC.obj.hom]
    (RC : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PC)
    (PJ : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PJ.obj.hom]
    (RJ : letI := picardCommGrpObj X.hom PC RC
      ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
        (fppfPicardSheaf (identityComponentOver PC.obj).hom).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PJ) :
    letI := picardCommGrpObj X.hom PC RC
    letI := picardCommGrpObj (identityComponentOver PC.obj).hom PJ RJ
    IsMonHom (picardIdentityComponentPullback (X := X) (Y := identityComponentOver PC.obj)
      PC RC PJ RJ (Curve.jacobianCurveMorphism hX o ho PC RC)) := by
  let := picardCommGrpObj X.hom PC RC
  let := picardCommGrpObj (identityComponentOver PC.obj).hom PJ RJ
  exact isMonHom_picardIdentityComponentPullback
    (X := X) (Y := identityComponentOver PC.obj)
    PC RC PJ RJ (Curve.jacobianCurveMorphism hX o ho PC RC)

end ActualAbelMap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardPullback_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardPullback_baseChange

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardPullbackUniversalPullbackIso_unit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardPullbackUniversalPullbackIso_unit

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentPullback_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardIdentityComponentPullback_baseChange
