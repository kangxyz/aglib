/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Ample
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Isogeny
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# The original theta principal isomorphism under the coherent-H1 bound

The actual theta morphism is monic and its original positive line bundle
is ample. The general dual criterion gives finite flat surjectivity under
the displayed original coherent-H1 inequality. Hence this same morphism is
an isomorphism. Its inverse is negative pullback by the original Abel map.
The H1 inequality remains an explicit premise; no target geometry is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Cohomology Scheme.Modules.Invertible
open Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

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
/-- The actual theta morphism is an isomorphism, conditional only on the
original coherent-H1 bound beyond the original curve and representatives. -/
theorem isIso_thetaLineBundleMorphism_of_structureH1_le (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    IsIso (lineBundleClassMorphismIdentityComponent J Q RQ
      (classOf (J).left (thetaLineBundle hX o ho P R hg))) := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let φ := lineBundleClassMorphismIdentityComponent J Q RQ
    (classOf (J).left (thetaLineBundle hX o ho P R hg))
  have hdata := finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le
    J Q RQ (thetaLineBundle hX o ho P R hg)
    (thetaLineBundle_isAmple hX o ho P R Q RQ hg) hH1
  have : IsFinite φ.left := hdata.1
  have : Flat φ.left := hdata.2.1
  have : Surjective φ.left := hdata.2.2
  have : Mono φ.left := mono_thetaLineBundleMorphism hX o ho P R Q RQ hg
  have : IsIso φ.left := Flat.isIso_of_surjective_of_mono φ.left
  have : IsIso ((Over.forget (Spec (.of k))).map φ) := by
    change IsIso φ.left
    infer_instance
  change IsIso φ
  exact isIso_of_reflects_iso φ (Over.forget (Spec (.of k)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism supplied by the original theta line bundle and original
representatives, retaining the original coherent-H1 premise. -/
def thetaPrincipalIsoOfStructureH1Le (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    J ≅ picardIdentityComponent (J).hom Q RQ := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  let := isIso_thetaLineBundleMorphism_of_structureH1_le hX o ho P R Q RQ hg hH1
  exact asIso (lineBundleClassMorphismIdentityComponent J Q RQ
    (classOf (J).left (thetaLineBundle hX o ho P R hg)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen isomorphism has the actual original theta morphism as hom. -/
@[simp]
theorem thetaPrincipalIsoOfStructureH1Le_hom (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    (thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1).hom =
      lineBundleClassMorphismIdentityComponent J Q RQ
        (classOf (J).left (thetaLineBundle hX o ho P R hg)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse is negative pullback along the original Abel map. -/
theorem thetaPrincipalIsoOfStructureH1Le_inv (hg : 0 < coherentGenus k X)
    (hH1 : letI := picardCommGrpObj X.hom P R
      Module.finrank k (structureCohomology k J 1) ≤
        Module.finrank k (Cotangent.Space η[J])) :
    letI := picardCommGrpObj X.hom P R
    letI : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
    letI : Smooth (J).hom := smooth_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI := picardCommGrpObj (J).hom Q RQ
    (thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1).inv =
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) ≫ ι[J] := by
  let := picardCommGrpObj X.hom P R
  let : IsHProjective (J).hom := isHProjective_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  let := picardCommGrpObj (J).hom Q RQ
  apply (cancel_epi (thetaPrincipalIsoOfStructureH1Le hX o ho P R Q RQ hg hH1).hom).mp
  rw [Iso.hom_inv_id, thetaPrincipalIsoOfStructureH1Le_hom, thetaAutoduality_leftInverse]

end AlgebraicGeometry.Scheme.OverField.Curve
