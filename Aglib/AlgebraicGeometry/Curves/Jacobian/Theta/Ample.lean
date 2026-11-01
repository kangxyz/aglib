/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AutodualityMorphism
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Effectivity
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Commutative
public import Aglib.AlgebraicGeometry.Group.Kernel.Monomorphism
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleCriterion

/-!
# Ampleness of the original theta line bundle

The original negative Abel pullback is a scheme left inverse to the theta
morphism. Thus its actual scheme kernel is the original base. The existing
effective finite-kernel ampleness theorem applies to the original theta
line bundle and its canonical nonzero section. No geometry of the dual
Picard component is used to prove this ampleness assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

local notation "J" => picardIdentityComponent X.hom P R

variable (Q : LocallyNoetherianOver (Spec (.of k)))
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual theta kernel structure morphism is an isomorphism to the
original field spectrum, including the full scheme structure. -/
theorem isIso_thetaLineBundleKernel (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    IsIso (Kernel.group (lineBundleClassIdentityComponentGroupHom J Q RQ
      (classOf (J).left (thetaLineBundle hX o ho P R hg)))).X.hom := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let p := lineBundleClassIdentityComponentGroupHom J Q RQ
    (classOf (J).left (thetaLineBundle hX o ho P R hg))
  have : Mono p.hom.hom.left := mono_thetaLineBundleMorphism hX o ho P R Q RQ hg
  exact Kernel.isIso_structureMap_of_mono p

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness concerns the original scheme kernel, without a point-count
or a reduced-kernel replacement. -/
theorem isFinite_thetaLineBundleKernel (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    IsFinite (Kernel.group (lineBundleClassIdentityComponentGroupHom J Q RQ
      (classOf (J).left (thetaLineBundle hX o ho P R hg)))).X.hom := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  have := isIso_thetaLineBundleKernel hX o ho P R Q RQ hg
  infer_instance

include Q RQ in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual positive line bundle of the original theta Cartier
divisor is ample. Only the original nonzero section and finite scheme
kernel enter the general projective-group criterion. -/
theorem thetaLineBundle_isAmple (hg : 0 < coherentGenus k X) :
    (thetaLineBundle hX o ho P R hg).IsAmple := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  exact isAmple_of_section_ne_zero_of_finite_identityComponent_kernel J Q RQ
    (thetaLineBundle hX o ho P R hg) (thetaSection hX o ho P R hg)
    (thetaSection_ne_zero hX o ho P R hg) (isFinite_thetaLineBundleKernel hX o ho P R Q RQ hg)

end AlgebraicGeometry.Scheme.OverField.Curve
