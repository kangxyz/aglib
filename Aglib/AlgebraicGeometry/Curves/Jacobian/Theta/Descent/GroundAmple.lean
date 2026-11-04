/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.BasedClassBaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.FieldBaseChange

/-! Ampleness of the original ground-field theta bundle. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Cohomology Scheme.RelativePicard Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  [IsSeparated Q.obj.hom]
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

include RQ in
/-- The original based theta bundle on the same Jacobian is ample over
the ground field. The original class comparison identifies its scalar
extension with the ample theta class for the lifted rational origin. -/
theorem thetaLineBundleGroundField_isAmple (hg : 0 < coherentGenus k X) :
    (thetaLineBundleGroundField hX o ho P R hg).IsAmple := by
  let K := AlgebraicClosure k
  let b := Spec.algebraMap k K
  let XK := fieldBaseChange K X
  let hXK := curveProperties_baseChange hX K b
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
  let J := picardIdentityComponent X.hom P R
  let JK := picardIdentityComponent XK.hom PK RK
  let QK := LocallyNoetherianOver.baseChange b Q
  let RQA := baseChangeRepresentableBy J.hom b Q RQ
  let : LocallyOfFiniteType QK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Q.obj.hom b))
  let : IsSeparated QK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd Q.obj.hom b))
  let e : fieldBaseChange K J ≅ JK := jacobianScalarExtensionIso P R K
  let RQK := picardSourceRepresentableBy e QK RQA
  let r := (PointDivisor.rationalPoint X o ho).baseChange b
  have hgen : coherentGenus K XK = coherentGenus k X :=
    coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b
  let hgK : 0 < coherentGenus K XK := hgen.symm ▸ hg
  let L := thetaLineBundleGroundField hX o ho P R hg
  let LK := thetaLineBundleGroundField hXK r.sectionMap r.section_comp PK RK hgK
  let thetaK := thetaLineBundle hXK r.sectionMap r.section_comp PK RK hgK
  have hEq : LK = thetaK :=
    thetaLineBundleGroundField_eq hXK r.sectionMap r.section_comp PK RK hgK
  have hThetaK : thetaK.IsAmple :=
    thetaLineBundle_isAmple hXK r.sectionMap r.section_comp PK RK QK RQK hgK
  have hLK : LK.IsAmple := hEq.symm ▸ hThetaK
  let : IsProper J.hom := isProper_identityComponentOver hX P R
  let : IsIso e.hom.left := (Over.forget (Spec (.of K))).map_isIso e.hom
  have hc : classOf (fieldBaseChange K J).left (pullbackLineBundle (pullback.fst J.hom b) L) =
      classOf (fieldBaseChange K J).left (pullbackLineBundle e.hom.left LK) :=
    pullbackClass_thetaLineBundleGroundField_fieldBaseChange hX o ho P R K hg
  exact LineBundle.IsAmple.of_fieldBaseChange J L K
    ((hLK.pullback_of_isAffineHom e.hom.left).of_classOf_eq hc.symm)

end AlgebraicGeometry.Scheme.OverField.Curve
