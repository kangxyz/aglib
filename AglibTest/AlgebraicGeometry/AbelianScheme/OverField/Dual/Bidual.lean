/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Bidual

/-! The canonical bidual construction keeps the supplied representatives
and needs no properness or geometric integrality assumption on Pic0(A). -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry Scheme.Modules.Invertible Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (Q : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q.obj.hom]
  (S : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

example : bidualMorphism A P R Q S ≫
    picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S =
      bidualPicardMorphism A P R Q S :=
  bidualMorphism_ι A P R Q S

example : η[A] ≫ bidualMorphism A P R Q S =
    η[picardIdentityComponent (picardIdentityComponent A.hom P R).hom Q S] :=
  bidualMorphism_pointed A P R Q S

example [IsSeparated Q.obj.hom] : IsMonHom (bidualMorphism A P R Q S) :=
  isMonHom_bidualMorphism A P R Q S

example (T : Over (Spec (.of k))) :
    pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map
      (1 : T ⟶ A)) (bidualFamilyClass A P R) = 0 :=
  bidualFamilyClass_pullback_one A P R T

example {T : Over (Spec (.of k))} (t : T ⟶ A) :
    ((fppfPicardSheaf (picardIdentityComponent A.hom P R).hom).obj.map
        ((t ≫ bidualMorphism A P R Q S) ≫
          picardIdentityComponentι (picardIdentityComponent A.hom P R).hom Q S).op).hom
      (S.homEquiv (𝟙 Q)) =
      ((quotientProjection (picardIdentityComponent A.hom P R).hom ≫
        toFppfPicardSheaf (picardIdentityComponent A.hom P R).hom).app (op T)).hom
          (pullbackClass ((familyScheme (picardIdentityComponent A.hom P R).hom).map t)
            (bidualFamilyClass A P R)) :=
  universalFppfClass_bidualMorphism A P R Q S t

example (L : LineBundle A.left) :
    RigidifiedPair.Iso
      (poincarePullback A P R
        (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)))
      (normalizedFamilyRigidifiedPair A.hom η[A].left (Over.w η[A]) A
        (translationFamilyLineBundle A (𝟙 A) L)) :=
  poincareLineBundleClassMorphismIso A P R L

example (L : LineBundle A.left) :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentPullback P R Q S
        (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)) =
      lineBundleClassMorphismIdentityComponent A P R (classOf A.left L) :=
  bidualMorphism_comp_dual_lineBundleClassMorphism A P R Q S L

variable (B : Over (Spec (.of k))) [GrpObj B]
  [IsProper B.hom] [GeometricallyIntegral B.hom]
  (P' : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P'.obj.hom]
  (R' : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf B.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P')
  (Q' : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType Q'.obj.hom]
  (S' : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent B.hom P' R').hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q')

example (f : A ⟶ B) [IsMonHom f] :
    bidualMorphism A P R Q S ≫
      picardIdentityComponentPullback Q' S' Q S
        (picardIdentityComponentPullback P R P' R' f) =
      f ≫ bidualMorphism B P' R' Q' S' :=
  bidualMorphism_naturality_of_isMonHom A B P R P' R' Q S Q' S' f

end
