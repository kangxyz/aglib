/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicImage
public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints

/-!
# The whole positive Abel morphism is a translate of the based morphism

The original origin graph ideal is the pullback of the original point ideal
on the curve. Consequently the positive family class is the based family
class plus the pullback of n times O(o). The same P/R classifies this identity
as an equality of whole scheme morphisms. No pointwise extensionality or
change of Picard representative is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

-- Keep the canonical identity-base fibre and the original family-base-change map.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The origin graph ideal on every test family is the pullback of the
actual ideal of the given rational point. -/
theorem originIdealClass_eq_pullback_pointIdeal (T : Over (Spec (.of k))) :
    classOf _ (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal X.hom o ho T.hom) =
      pullbackClass (pullback.fst X.hom T.hom)
        (classOf X.left (PointDivisor.idealLineBundle X hX o ho)) := by
  have hbase : classOf _
      (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal X.hom o ho (𝟙 _)) =
      pullbackClass (pullback.fst X.hom (𝟙 _))
        (classOf X.left (PointDivisor.idealLineBundle X hX o ho)) := by
    simpa only [Hom.originIdealLineBundle, Category.id_comp] using
      (pointIdeal_class_pullback_identity X hX o ho).symm
  have h := originIdealClass_baseChange Hom.smoothRelativeDivisorIdeal
    Hom.relativeCartierIdealBaseChange X.hom o ho (𝟙 _) T.hom T.hom (Category.comp_id _)
  rw [hbase] at h
  rw [← h, ← pullbackClass_comp, Hom.familyMap_fst]

/-- The original origin ideal has the negative of the positive point class,
after the actual family pullback. -/
theorem originIdealClass_eq_neg_pullback_positive (T : Over (Spec (.of k))) :
    classOf _ (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal X.hom o ho T.hom) =
      -pullbackClass (pullback.fst X.hom T.hom)
        (classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  rw [originIdealClass_eq_pullback_pointIdeal hX o ho T]
  change pullbackClass _ (classOf _ (PointDivisor.idealLineBundle X hX o ho)) =
    -pullbackClass _ (-classOf _ (PointDivisor.idealLineBundle X hX o ho))
  rw [PullbackTensor.Local.pullbackClass_neg, neg_neg]

/-- Positive degree before normalization, as a whole original family class. -/
theorem positiveFamilyLineBundle_class_eq_based_add_point (n : ℕ) :
    classOf _ (positiveFamilyLineBundle X.hom n) = classOf _ (lineBundle X.hom o ho n) +
      pullbackClass (pullback.fst X.hom (parameter X.hom n).hom)
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  rw [positiveFamilyLineBundle_class_eq_based_sub_origin X.hom o ho n,
    originIdealClass_eq_neg_pullback_positive hX o ho (parameter X.hom n),
    smul_neg, sub_neg_eq_add]
  change _ = _ + (PullbackTensor.Local.pullbackHom _) (n • _)
  rw [map_nsmul]
  rfl

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

-- Type the original terminal test map and original identity-base class explicitly.
omit [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant Picard morphism classifies the original curve class pulled
back to the whole test family, on the same represented test site. -/
theorem homEquiv_constant_picardPoint (T : LocallyNoetherianOver (Spec (.of k)))
    (c : PicardGroup X.left) :
    R.homEquiv (ObjectProperty.homMk (toUnit T.obj ≫ picardPoint P R c)) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (pullbackClass (pullback.fst X.hom T.obj.hom) c) := by
  let a : T ⟶ locallyNoetherianRationalPoint k := ObjectProperty.homMk (toUnit T.obj)
  let b : locallyNoetherianRationalPoint k ⟶ P := ObjectProperty.homMk (picardPoint P R c)
  change R.homEquiv (a ≫ b) = _
  rw [R.homEquiv_comp, homEquiv_picardPoint, picardPointClass_apply]
  have h := (NatTrans.naturality_apply
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom) (toUnit T.obj).op
    (pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) c)).symm
  refine h.trans ?_
  change (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
    (pullbackClass ((familyScheme X.hom).map (toUnit T.obj))
      (pullbackClass (pullback.fst X.hom (𝟙 _)) c)) = _
  have hfst : (familyScheme X.hom).map (toUnit T.obj) ≫
      pullback.fst X.hom (𝟙 (Spec (.of k))) = pullback.fst X.hom T.obj.hom :=
    familyScheme_map_fst X.hom (toUnit T.obj)
  rw [← pullbackClass_comp, hfst]

variable [LocallyOfFiniteType P.obj.hom]

-- The same representing equivalence compares the whole morphisms before evaluation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The positive Abel map is the original based Abel map multiplied by the
constant point n[O(o)], as a whole morphism to the same Picard scheme. -/
theorem positiveAbelMorphism_eq_based_mul_constant (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (positiveAbelMorphism X P R n).hom = (abelMorphism o ho P R n).hom *
      (toUnit (locallyNoetherianParameter X n).obj ≫
        picardPoint P R (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))) := by
  let := picardCommGrpObj X.hom P R
  have h : positiveAbelMorphism X P R n = ObjectProperty.homMk
      ((abelMorphism o ho P R n).hom * (toUnit (locallyNoetherianParameter X n).obj ≫
        picardPoint P R (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))) := by
    have hbase : R.homEquiv (ObjectProperty.homMk (abelMorphism o ho P R n).hom) =
        abelSection X o ho n := homEquiv_abelMorphism o ho P R n
    have hconstant := homEquiv_constant_picardPoint P R (locallyNoetherianParameter X n)
      (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
    have hclasses : positiveAbelSection X n = abelSection X o ho n +
        (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (parameter X.hom n))
          (pullbackClass (pullback.fst X.hom (parameter X.hom n).hom)
            (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))) := by
      exact (congrArg (fun c : PicardGroup (pullback X.hom (parameter X.hom n).hom) =>
        (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
          (op (parameter X.hom n)) c)
        (positiveFamilyLineBundle_class_eq_based_add_point hX o ho n)).trans (map_add _ _ _)
    apply R.homEquiv.injective
    exact (homEquiv_positiveAbelMorphism X P R n).trans (hclasses.trans
      ((congrArg₂ (fun a b : (fppfPicardSheaf X.hom).obj.obj (op (parameter X.hom n)) =>
        a + b) hbase.symm hconstant.symm).trans
          (picard_homEquiv_mul X.hom P R _ _).symm))
  exact congrArg InducedCategory.Hom.hom h

/-- The same equality through the existing native translation isomorphism. -/
theorem positiveAbelMorphism_eq_based_comp_translation (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (positiveAbelMorphism X P R n).hom = (abelMorphism o ho P R n).hom ≫
      (GrpObj.mulRight (picardPoint P R
        (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))).hom := by
  let := picardCommGrpObj X.hom P R
  rw [positiveAbelMorphism_eq_based_mul_constant hX o ho P R n]
  simp only [GrpObj.mulRight, Hom.mul_def, CartesianMonoidalCategory.comp_lift_assoc,
    Category.comp_id, comp_toUnit_assoc]

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
