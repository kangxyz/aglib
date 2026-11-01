/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicTranslation
public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree

/-!
# The existing degree stratum is a translate of the same Jacobian

Keep the original Kleiman Euler-condition open and its inverse-line-bundle
polynomial m deg O(1)+1-g-n. Translation by n[O(o)] identifies its inverse
image with the original identity component, using the already proved
degree-zero component criterion. The canonical restriction of that SAME
translation isomorphism then gives the actual scheme isomorphism, with
its ambient inclusion equation retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry ProjectiveSpace
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.RelativePicard.Strata
open Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {index : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace k index) [IsClosedImmersion i] {N : ℕ} (e : index ≃ Fin (N + 1))
  (hX : Properties (Over.mk (i ≫ toSpec k index) : FScheme k))
  (o : Spec (.of k) ⟶ Y) (ho : o ≫ (i ≫ toSpec k index) = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k index)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse image of the EXISTING degree-n Euler open under the
original positive translation is the SAME identity component. -/
theorem preimage_translation_degreeStratum_eq_identityComponent (n : ℕ) :
    letI := hX.flat
    letI := picardCommGrpObj (i ≫ toSpec k index) P R
    (GrpObj.mulRight (picardPoint (X := Over.mk (i ≫ toSpec k index)) P R
      (n • classOf Y
        (PointDivisor.positiveLineBundle (Over.mk (i ≫ toSpec k index)) hX o ho)))).hom.left ⁻¹'
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens (T := P.obj)
        (R.homEquiv (𝟙 P)) : Set P.obj.left) = identityComponent P.obj := by
  let := hX.flat
  let := hX.proper
  let := hX.isGeometricallyIntegral
  let := picardCommGrpObj (i ≫ toSpec k index) P R
  let X : FScheme k := Over.mk (i ≫ toSpec k index)
  let : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  let E := picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral
    (X := X) P R
  have htrans (c d : PicardGroup Y) :
      picardPoint (X := X) P R c ≫ (GrpObj.mulRight (picardPoint (X := X) P R d)).hom =
        picardPoint (X := X) P R (c + d) := by
    have hadd : picardPoint (X := X) P R (c + d) =
        picardPoint (X := X) P R c * picardPoint (X := X) P R d := by
      have h := congrArg Additive.toMul (E.map_add c d)
      change Additive.toMul (E (c + d)) = Additive.toMul (E c) * Additive.toMul (E d) at h
      simpa only [E,
        picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply] using h
    rw [hadd]
    simp only [GrpObj.mulRight, CategoryTheory.Hom.mul_def,
      CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, comp_toUnit_assoc,
      toUnit_unit, Category.id_comp]
  let c := n • classOf Y (PointDivisor.positiveLineBundle X hX o ho)
  let τ := GrpObj.mulRight (picardPoint (X := Over.mk (i ≫ toSpec k index)) P R c)
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  let Z : Set P.obj.left := τ.hom.left ⁻¹' (U : Set P.obj.left)
  have hc : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c = (n : ℤ) := by
    dsimp only [c]
    rw [map_nsmul]
    exact (congrArg (fun z : ℤ => n • z)
      (curveDegree_positiveLineBundle (X := X) hX o ho)).trans (by simp)
  have hZ : IsClopen Z :=
    (isClopen_opens_eulerCondition_degreeStratumPolynomial i e P R hX n).preimage
      τ.hom.left.continuous
  have hunit : Group.unitPoint P.obj ∈ Z := by
    have hu : η[P.obj] ≫ τ.hom = picardPoint (X := Over.mk (i ≫ toSpec k index)) P R c := by
      simpa only [picardPoint_zero, zero_add] using htrans 0 c
    change (η[P.obj] ≫ τ.hom).left (IsLocalRing.closedPoint k) ∈ U
    rw [hu]
    exact (picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff
      i e P R hX c n).mpr hc
  have hZdeg (d : PicardGroup Y)
      (hd : (picardPoint (X := X) P R d).left (IsLocalRing.closedPoint k) ∈ Z) :
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX d = 0 := by
    change (picardPoint (X := X) P R d ≫ τ.hom).left (IsLocalRing.closedPoint k) ∈ U at hd
    rw [htrans d c] at hd
    have h := (picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff
      i e P R hX (d + c) n).mp hd
    change (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX) (d + c) = (n : ℤ) at h
    rw [map_add, hc] at h
    omega
  exact (identityComponent_eq_of_isClopen_of_isAlgClosed hX P R Z hZ hunit hZdeg).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict the original translation isomorphism to the existing degree
stratum, using only the native equality-of-opens isomorphism. -/
def degreeStratumTranslationIso (n : ℕ) :
    letI := hX.flat
    letI := picardCommGrpObj (i ≫ toSpec k index) P R
    (identityComponentOver P.obj).left ≅
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
        (T := P.obj) (R.homEquiv (𝟙 P))).toScheme := by
  let := hX.flat
  let := picardCommGrpObj (i ≫ toSpec k index) P R
  let U := (eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
    (T := P.obj) (R.homEquiv (𝟙 P))
  let τ := GrpObj.mulRight (picardPoint (X := Over.mk (i ≫ toSpec k index)) P R
    (n • classOf Y (PointDivisor.positiveLineBundle (Over.mk (i ≫ toSpec k index)) hX o ho)))
  have hU : τ.hom.left ⁻¹ᵁ U = identityComponent P.obj :=
    SetLike.coe_injective (preimage_translation_degreeStratum_eq_identityComponent
      i e hX o ho P R n)
  exact (P.obj.left.isoOfEq hU.symm) ≪≫ asIso (τ.hom.left ∣_ U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-stratum identification preserves the literal original
component inclusion followed by the same positive translation. -/
theorem degreeStratumTranslationIso_hom_ι (n : ℕ) :
    letI := hX.flat
    letI := picardCommGrpObj (i ≫ toSpec k index) P R
    (degreeStratumTranslationIso i e hX o ho P R n).hom ≫
      ((eulerCondition i N e (degreeStratumPolynomial i hX n)).opens
        (T := P.obj) (R.homEquiv (𝟙 P))).ι =
      (identityComponentι P.obj).left ≫ (GrpObj.mulRight
        (picardPoint (X := Over.mk (i ≫ toSpec k index)) P R
        (n • classOf Y
          (PointDivisor.positiveLineBundle (Over.mk (i ≫ toSpec k index)) hX o ho)))).hom.left := by
  let := hX.flat
  let := picardCommGrpObj (i ≫ toSpec k index) P R
  dsimp only [degreeStratumTranslationIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  rfl

end AlgebraicGeometry.Scheme.OverField.Curve
