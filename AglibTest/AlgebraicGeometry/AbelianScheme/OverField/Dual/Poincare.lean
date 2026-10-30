/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare

/-! The original universal bundle, its literal Pic0 restriction and both
unit normalizations, with no smoothness/properness/dimension assumption on Pic0. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry Scheme.Modules.Invertible Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom]
  (P : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example : poincareLineBundle G P R =
    pullbackLineBundle ((familyScheme G.hom).map (picardIdentityComponentι G.hom P R))
      (picardUniversalLineBundle G P R) :=
  poincareLineBundle_eq_pullback G P R

example {T : Over (Spec (.of k))} (f : T ⟶ picardIdentityComponent G.hom P R) :
    RigidifiedPair G.hom η[G].left (by simp) T :=
  poincarePullback G P R f

example {T : Scheme.LocallyNoetherianOver (Spec (.of k))}
    (f : T.obj ⟶ picardIdentityComponent G.hom P R) :
    ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
        (classOf _ (poincarePullback G P R f).bundle) =
      R.homEquiv (ObjectProperty.homMk (f ≫ picardIdentityComponentι G.hom P R)) :=
  poincarePullback_fppfClass G P R f

example (T : Over (Spec (.of k))) :
    (Scheme.Modules.pullback (originSection G.hom η[G].left (by simp) T)).map
        (poincareUnitIso G P R T).iso.hom ≫
      (trivialRigidifiedPair G.hom η[G].left (by simp) T).rigidification.hom =
        (poincarePullback G P R (1 : T ⟶ picardIdentityComponent G.hom P R)).rigidification.hom :=
  (poincareUnitIso G P R T).comm

example :
    (Scheme.Modules.pullback
      (lift (𝟙 G) (1 : G ⟶ picardIdentityComponent G.hom P R)).left).obj
        (poincareLineBundle G P R).val ≅
          (SheafOfModules.unit G.left.ringCatSheaf : G.left.Modules) :=
  poincareParameterUnitIso G P R

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.poincarePullback_fppfClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms poincarePullback_fppfClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.poincarePullbackCompIso_assoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms poincarePullbackCompIso_assoc

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.poincareUnitIso_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms poincareUnitIso_naturality

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.poincareParameterUnitIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms poincareParameterUnitIso
