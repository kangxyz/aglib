/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.FamilyFormula
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.SourcePullback
public import Aglib.AlgebraicGeometry.Picard.Scheme.Pullback

/-!
# Source pullback of the original line-bundle morphism

Whole translated-family classes are compared on arbitrary test schemes
before applying the original relative Picard quotient. The represented
morphisms and their actual identity-component restrictions retain the
supplied groups, Picard representatives and normalizing units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj
open AlgebraicGeometry Scheme Scheme.Group Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The whole original translated class commutes with source-group pullback, on every test. -/
theorem translationFamilyClass_sourceHom
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] {T : Over (Spec (.of k))} (t : T ⟶ A)
    (a : PicardGroup B.left) :
    pullbackClass (familyMapOfHom f T) (translationFamilyClass B (t ≫ f) a) =
      translationFamilyClass A t (pullbackClass f.left a) := by
  have hm : ((fst A T ≫ f) * (snd A T ≫ (t ≫ f))) =
      translationFamilyMorphism A t ≫ f := by
    simp only [translationFamilyMorphism, MonObj.mul_comp, Category.assoc]
  have H := pullbackClass_familyMapOfHom_translationFamilyClass B f (t ≫ f) a
  rw [hm, Over.comp_left, pullbackClass_comp] at H
  exact H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original represented line-bundle map is contravariantly functorial in the source. -/
theorem lineBundleClassMorphism_sourceHom
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Flat A.hom] [GeometricallyIntegral A.hom]
    [IsProper B.hom] [Flat B.hom] [GeometricallyIntegral B.hom]
    (PA : LocallyNoetherianOver (Spec (.of k)))
    (RA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PA)
    (PB : LocallyNoetherianOver (Spec (.of k)))
    (RB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf B.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PB)
    (f : A ⟶ B) [IsMonHom f] (a : PicardGroup B.left) :
    lineBundleClassMorphism A PA RA (pullbackClass f.left a) =
      f ≫ lineBundleClassMorphism B PB RB a ≫ picardPullback PA RA PB RB f := by
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨A, LocallyOfFiniteType.isLocallyNoetherian A.hom⟩
  let q : PicardGroup (pullback A.hom A.hom) →+
      (fppfPicardSheaf A.hom).obj.obj (op A) :=
    ((quotientProjection A.hom ≫ toFppfPicardSheaf A.hom).app (op A)).hom
  have hleft := fppf_homEquiv_comp_lineBundleClassMorphism A PA RA (T := T)
    (𝟙 A) (pullbackClass f.left a)
  rw [Category.id_comp] at hleft
  have hright := homEquiv_comp_picardPullback (X := A) (Y := B) PA RA PB RB f
    (T := T) (f ≫ lineBundleClassMorphism B PB RB a)
  have hphi := fppf_homEquiv_comp_lineBundleClassMorphism B PB RB (T := T) f a
  rw [hphi] at hright
  have hclass := translationFamilyClass_sourceHom f (T := A) (𝟙 A) a
  rw [Category.id_comp] at hclass
  have hsource := fppfPicardPullback_class f A (translationFamilyClass B f a)
  have hfull : (ObjectProperty.homMk
      (lineBundleClassMorphism A PA RA (pullbackClass f.left a)) : T ⟶ PA) =
      ObjectProperty.homMk
        ((f ≫ lineBundleClassMorphism B PB RB a) ≫ picardPullback PA RA PB RB f) := by
    apply RA.homEquiv.injective
    have hc := congrArg q hclass.symm
    exact hleft.trans (hc.trans (hsource.trans hright.symm))
  have H := congrArg (fun v : T ⟶ PA => v.hom) hfull
  exact H.trans (Category.assoc _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same source law holds on the actual original Picard identity components. -/
theorem lineBundleClassMorphismIdentityComponent_sourceHom
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Flat A.hom] [GeometricallyIntegral A.hom]
    [IsProper B.hom] [Flat B.hom] [GeometricallyIntegral B.hom]
    (PA : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PA.obj.hom]
    (RA : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PA)
    (PB : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PB.obj.hom]
    (RB : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf B.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PB)
    (f : A ⟶ B) [IsMonHom f] (a : PicardGroup B.left) :
    lineBundleClassMorphismIdentityComponent A PA RA (pullbackClass f.left a) =
      f ≫ lineBundleClassMorphismIdentityComponent B PB RB a ≫
        picardIdentityComponentPullback (X := A) (Y := B) PA RA PB RB f := by
  let := picardCommGrpObj A.hom PA RA
  let := picardCommGrpObj B.hom PB RB
  apply (cancel_mono (picardIdentityComponentι A.hom PA RA)).mp
  rw [lineBundleClassMorphismIdentityComponent_ι]
  simp only [Category.assoc, picardIdentityComponentPullback_ι,
    lineBundleClassMorphismIdentityComponent_ι_assoc]
  exact lineBundleClassMorphism_sourceHom A B PA RA PB RB f a

end AlgebraicGeometry.Scheme.RelativePicard
