/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.H1
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.FieldComparison

/-!
# Thin canonical principal consumers of the original general coherent-H1 bound

The same curve Picard representative, identity component, and canonical Abel
dual morphism are retained. The general coherent-H1 bound is applied to that same original Jacobian.
No rational origin or ground-field theta line bundle is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry Scheme.RelativePicard Scheme.Cohomology Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

local notation "J" => picardIdentityComponent X.hom P R

include hX in
/-- The general bound is applied to the same original Jacobian, not its dual. -/
theorem jacobianStructureH1Le :
    letI := picardCommGrpObj X.hom P R
    Module.finrank k (structureCohomology k J 1) ≤
      Module.finrank k (Cotangent.Space η[J]) := by
  let := picardCommGrpObj X.hom P R
  let : IsProper (J).hom := isProper_identityComponentOver hX P R
  let : Smooth (J).hom := smooth_identityComponentOver hX P R
  let : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
  exact AlgebraicGeometry.Scheme.Group.finrank_structureH1_le_finrank_identityCotangent J

variable
  (Q : LocallyNoetherianOver (Spec (.of k)))
  (RQ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (picardIdentityComponent X.hom P R).hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)
  [LocallyOfFiniteType Q.obj.hom] [IsSeparated Q.obj.hom]

/-- The existing origin-free canonical map with its H1 premise discharged. -/
def canonicalJacobianAbelDualMorphism :=
  canonicalAbelDualMorphism hX P R Q RQ (jacobianStructureH1Le hX P R)

/-- The original canonical dual map is an isomorphism over the ground field. -/
theorem isIso_canonicalJacobianAbelDualMorphism :
    IsIso (canonicalJacobianAbelDualMorphism hX P R Q RQ) := by
  exact isIso_canonicalAbelDualMorphism hX P R Q RQ (jacobianStructureH1Le hX P R)

/-- A supplied curve origin identifies the same canonical dual map with
pullback along the original Abel map over the original field. -/
theorem canonicalJacobianAbelDualMorphism_eq_originalPullback
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    canonicalJacobianAbelDualMorphism hX P R Q RQ =
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) := by
  exact canonicalAbelDualMorphism_eq_originalPullback hX P R Q RQ
    (jacobianStructureH1Le hX P R) o ho

/-- Reuse the existing negative-inverse group isomorphism on the same J and D. -/
def canonicalJacobianPrincipalGroupIso :=
  canonicalThetaPrincipalGroupIso hX P R Q RQ (jacobianStructureH1Le hX P R)

/-- The underlying scheme isomorphism is obtained from that same group isomorphism. -/
def canonicalJacobianPrincipalIso :=
  canonicalThetaPrincipalIso hX P R Q RQ (jacobianStructureH1Le hX P R)

/-- The canonical principal hom is the negative inverse of the original dual map. -/
theorem canonicalJacobianPrincipalIso_hom :
    letI := picardCommGrpObj X.hom P R
    letI := isIso_canonicalJacobianAbelDualMorphism hX P R Q RQ
    (canonicalJacobianPrincipalIso hX P R Q RQ).hom =
      ι[J] ≫ (asIso (canonicalJacobianAbelDualMorphism hX P R Q RQ)).inv := by
  exact canonicalThetaPrincipalIso_hom hX P R Q RQ (jacobianStructureH1Le hX P R)

/-- The inverse of the same principal isomorphism is the original dual map
followed by inversion on the original Jacobian. -/
theorem canonicalJacobianPrincipalIso_inv :
    letI := picardCommGrpObj X.hom P R
    (canonicalJacobianPrincipalIso hX P R Q RQ).inv =
      canonicalJacobianAbelDualMorphism hX P R Q RQ ≫ ι[J] := by
  let := picardCommGrpObj X.hom P R
  let := isIso_canonicalJacobianAbelDualMorphism hX P R Q RQ
  apply (cancel_epi (canonicalJacobianPrincipalIso hX P R Q RQ).hom).mp
  rw [Iso.hom_inv_id, canonicalJacobianPrincipalIso_hom]
  rw [Category.assoc]
  let e := asIso (canonicalJacobianAbelDualMorphism hX P R Q RQ)
  change 𝟙 J = ι[J] ≫ e.inv ≫ e.hom ≫ ι[J]
  rw [← Category.assoc e.inv e.hom (ι[J]), e.inv_hom_id,
    Category.id_comp, GrpObj.inv_comp_inv]

/-- With any supplied origin, its inverse is negative original Abel pullback. -/
theorem canonicalJacobianPrincipalIso_inv_originalPullback
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    letI := picardCommGrpObj X.hom P R
    (canonicalJacobianPrincipalIso hX P R Q RQ).inv =
      picardIdentityComponentPullback P R Q RQ (jacobianCurveMorphism hX o ho P R) ≫ ι[J] := by
  let := picardCommGrpObj X.hom P R
  rw [canonicalJacobianPrincipalIso_inv,
    canonicalJacobianAbelDualMorphism_eq_originalPullback hX P R Q RQ o ho]

/-- The same canonical principal map becomes the morphism of an ample line
bundle on the actual scalar-extended Jacobian in positive genus. The original
field-comparison theorem supplies the full statement and all native parents. -/
theorem canonicalJacobianPrincipalIso_geometricPositive
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let A := fieldBaseChange K J
    let Q' := LocallyNoetherianOver.baseChange b Q
    let RQA := baseChangeRepresentableBy (J).hom b Q RQ
    let scalarGroup : GrpObj A := Functor.grpObjObj (F := Over.pullback b) (G := J)
    letI : GrpObj A := scalarGroup
    letI : IsProper (J).hom := isProper_identityComponentOver hX P R
    letI : GeometricallyIntegral (J).hom := geometricallyIntegral_identityComponentOver hX P R
    letI : IsProper A.hom := by change IsProper (pullback.snd (J).hom b); infer_instance
    letI : GeometricallyIntegral A.hom := by
      change GeometricallyIntegral (pullback.snd (J).hom b); infer_instance
    let eD := Over.isoMk (picardIdentityComponentBaseChangeIso (J).hom Q RQ K)
      (picardIdentityComponentBaseChangeIso_hom_comp (J).hom Q RQ K)
    ∃ L : LineBundle A.left, L.IsAmple ∧
      (Over.pullback b).map (canonicalJacobianPrincipalIso hX P R Q RQ).hom ≫ eD.hom =
        lineBundleClassMorphismIdentityComponent A Q' RQA (classOf A.left L) := by
  exact canonicalThetaPrincipalIso_geometricPositive hX P R Q RQ
    (jacobianStructureH1Le hX P R) K hg

end AlgebraicGeometry.Scheme.OverField.Curve
