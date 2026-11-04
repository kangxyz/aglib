/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelDegreeZeroChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointRepresentedPicardChart

/-! # The original Abel class in the original Picard H¹ map -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Scheme.RelativePicard Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.Modules.Invertible Scheme.EtaleCohomology.Picard RepresentedKernel
open GroupCohomology.Kummer.Coefficients

universe u dZ dX w s e

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Base k ⟶ X.left) (ho : o ≫ X.hom = 𝟙 (Base k))
  [IsLocallyNoetherian X.left]
  (P : LocallyNoetherianOver (Base k)) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Base k)).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

set_option hygiene false in
local notation "Z" => pullback X.hom X.hom
set_option hygiene false in
local notation "π" => pullback.snd X.hom X.hom

variable [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X.left)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Z)]
  [∀ U : X.left.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology Z).over
    ((siteBaseChange π).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : X.left.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom π))]
  (o' : X.left ⟶ Z) (ho' : o' ≫ π = 𝟙 X.left)
  [IsProper π] [Flat π] [GeometricallyIntegral π]

/-- The original Abel graph and degree-zero inclusion give the whole H¹ map of the
original Abel class on the original product, for any supplied section of its second projection. -/
theorem jacobianAbelPicardH1 :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    let J := picardIdentityComponent X.hom P R
    letI : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
    let G := (groupSchemeBaseChange X.hom).functor.obj (Grp.mk J)
    let y := jacobianAbelTerminalGraph hX o ho P R
    let C := Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho X.hom
      (𝟙 X.left) (Category.id_comp X.hom)
    let c : Sheaf.H.{w} (gm Z) 1 := picardCohomologyEquiv Z C
    let j := picardDegreeZeroEtaleInclusion P R X.hom o' ho'
    let a := representedIntegerSection G y
    let U := (constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X.left) 1
    let e₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (AbelianSheaf.{u, u + 1} X.left) 1).app U
    let ep := ((higherDirectImageIso π 1).app (gm Z)).symm ≪≫
      gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} π o' ho'
    let x := cohomologyOriginalDerivedAdjunct π (gm Z) c
    H.map x = e₁.hom ≫ a ≫ j ≫ ep.inv := by
  intro J G y C c j a U H e₁ ep x
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let : IsCommMonObj J := inferInstanceAs (IsCommMonObj (identityComponentOver P.obj))
  let Q := LocallyNoetherianOver.baseChange X.hom P
  let RQ := baseChangeRepresentableBy X.hom X.hom P R
  let : LocallyOfFiniteType Q.obj.hom :=
    Scheme.locallyOfFiniteType_over_pullback_obj_hom X.hom P.obj
  have hValue := jacobianAbelTerminalGraphNormalizedValue hX o ho P R o' ho'
  have hNorm := Kummer.NormalizedChartFamilyValue.eq π o' ho' Q RQ
    (etaleTerminal X.left) hValue
  have hClass : (picardCohomologyEquiv Z).symm c = C :=
    (picardCohomologyEquiv Z).symm_apply_apply C
  have hH1 := gmDerivedAdjunctH1OfRepresentedChartValue π o' ho' j y c C hClass hNorm
  have hEp : H.map x ≫ ep.hom = e₁.hom ≫ a ≫ j := hH1
  have h := (Iso.eq_comp_inv ep).mpr hEp
  simpa only [Category.assoc] using h

end AlgebraicGeometry.Scheme.OverField.Curve
