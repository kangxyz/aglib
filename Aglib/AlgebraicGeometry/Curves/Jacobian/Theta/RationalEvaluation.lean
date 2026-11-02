/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationFibre
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.UniversalFibre

/-!
# Rational specialization on the original curve

The inverse of the canonical identity-base first projection identifies
the already constructed evaluation fibre with the original curve X. The
original evaluation immersion is pulled back through that same map. Its
actual ideal comparison, coefficient class and structural cohomology are
retained; this introduces no second global evaluation family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
  (c : 𝟙_ (Over (Spec (.of k))) ⟶ thetaParameterOver hX o ho P R)

/-- The same original rational fibre, viewed from the original curve by
the inverse of the canonical identity-base first projection. -/
def thetaRationalFamilyMap : X.left ⟶ pullback X.hom (thetaParameterOver hX o ho P R).hom :=
  inv (pullback.fst X.hom (𝟙 (Spec (.of k)))) ≫ (familyScheme X.hom).map c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original-X specialization is the actual cartesian family square. -/
theorem isPullback_thetaRationalFamilyMap :
    IsPullback (thetaRationalFamilyMap hX o ho P R c) X.hom
      (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) c.left := by
  let e := inv (pullback.fst X.hom (𝟙 (Spec (.of k))))
  have he : e ≫ pullback.snd X.hom (𝟙 (Spec (.of k))) = X.hom := by
    have h := pullback.condition (f := X.hom) (g := 𝟙 (Spec (.of k)))
    simp only [Category.comp_id] at h
    rw [← h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have H : IsPullback e X.hom (pullback.snd X.hom (𝟙 (Spec (.of k))))
      (𝟙 (Spec (.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  let m : pullback X.hom (𝟙 (Spec (.of k))) ⟶
      pullback X.hom (thetaParameterOver hX o ho P R).hom := (familyScheme X.hom).map c
  have H0 : IsPullback m (pullback.snd X.hom (𝟙 (Spec (.of k))))
      (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) c.left :=
    isPullback_familyScheme_map X.hom c
  change IsPullback (e ≫ m) X.hom
    (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) c.left
  simpa only [Category.id_comp] using H.paste_horiz H0

/-- The original evaluation immersion after that same rational specialization. -/
def thetaRationalEvaluationInclusion :
    pullback (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      (thetaRationalFamilyMap hX o ho P R c) ⟶ X.left := pullback.snd _ _

/-- Actual Cartierness and flatness survive the rational specialization. -/
theorem thetaRationalEvaluation_isRelativeEffectiveCartier :
    Hom.IsRelativeEffectiveCartier (thetaRationalEvaluationInclusion hX o ho P R c) X.hom :=
  (thetaEvaluation_isRelativeEffectiveCartier hX o ho P R).of_isPullback
    (isPullback_thetaRationalFamilyMap hX o ho P R c) (IsPullback.of_hasPullback _ _)

/-- Finiteness is retained by the actual composite pullback square. -/
theorem thetaRationalEvaluation_finite :
    IsFinite (thetaRationalEvaluationInclusion hX o ho P R c ≫ X.hom) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback _ _).paste_vert (isPullback_thetaRationalFamilyMap hX o ho P R c))
    (thetaEvaluation_finite_flat hX o ho P R).1

/-- The positive coefficient from the already selected field fibre,
transported through the canonical identity-base isomorphism. -/
def thetaRationalEvaluationLineBundle : LineBundle X.left :=
  pullbackLineBundle (inv (pullback.fst X.hom (𝟙 (Spec (.of k)))))
    (thetaEvaluationFibrePositiveLineBundle hX o ho P R (𝟙 (Spec (.of k))) c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rational coefficient is the positive bundle of the ACTUAL
specialized ideal, with both ideal comparisons from the same global divisor. -/
theorem thetaRationalEvaluation_idealClass :
    classOf X.left (dualLineBundle X.left
      (thetaRationalEvaluation_isRelativeEffectiveCartier hX o ho P R c).idealLineBundle) =
      classOf X.left (thetaRationalEvaluationLineBundle hX o ho P R c) := by
  let hD := thetaEvaluation_isRelativeEffectiveCartier hX o ho P R
  let e := inv (pullback.fst X.hom (𝟙 (Spec (.of k))))
  let m : pullback X.hom (𝟙 (Spec (.of k))) ⟶
      pullback X.hom (thetaParameterOver hX o ho P R).hom := (familyScheme X.hom).map c
  have hrat := hD.pullbackClass_classOf_idealLineBundle
    (isPullback_thetaRationalFamilyMap hX o ho P R c) (IsPullback.of_hasPullback _ _)
  have hfib := hD.pullbackClass_classOf_idealLineBundle
    (isPullback_familyScheme_map X.hom c) (IsPullback.of_hasPullback _ _)
  let hF := thetaEvaluationFibre_isRelativeEffectiveCartier hX o ho P R (𝟙 (Spec (.of k))) c
  change -classOf X.left
    (thetaRationalEvaluation_isRelativeEffectiveCartier hX o ho P R c).idealLineBundle =
      classOf X.left (pullbackLineBundle e
        (thetaEvaluationFibrePositiveLineBundle hX o ho P R (𝟙 (Spec (.of k))) c))
  rw [← pullbackClass_classOf]
  change -classOf X.left
    (thetaRationalEvaluation_isRelativeEffectiveCartier hX o ho P R c).idealLineBundle =
      pullbackClass e (-classOf _
        hF.idealLineBundle)
  rw [PullbackTensor.Local.pullbackClass_neg]
  apply congrArg Neg.neg
  exact hrat.symm.trans ((pullbackClass_comp e m (classOf _ hD.idealLineBundle)).trans
    (congrArg (pullbackClass e) hfib))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All cohomology dimensions retain the original structural field action
through the canonical identity-base isomorphism. -/
theorem thetaRationalEvaluation_dimension (n : ℕ) :
    Module.finrank k (moduleCohomology k X
      (thetaRationalEvaluationLineBundle hX o ho P R c).val n) =
      Module.finrank k (fibreCohomology
        (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
        (thetaUniversalPair hX o ho P R).bundle.val k c.left n) := by
  let Y : FScheme k := Over.mk (pullback.snd X.hom (𝟙 (Spec (.of k))))
  let B : LineBundle Y.left :=
    thetaEvaluationFibrePositiveLineBundle hX o ho P R (𝟙 (Spec (.of k))) c
  let e := inv (pullback.fst X.hom (𝟙 (Spec (.of k))))
  have he : e ≫ Y.hom = X.hom := by
    have h := pullback.condition (f := X.hom) (g := 𝟙 (Spec (.of k)))
    simp only [Category.comp_id] at h
    change e ≫ pullback.snd X.hom (𝟙 (Spec (.of k))) = X.hom
    rw [← h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  calc
    _ = moduleCohomologyDimension X.hom (pullbackLineBundle e B).val n :=
      (moduleCohomologyDimension_eq_finrank_moduleCohomology X (pullbackLineBundle e B).val n).symm
    _ = moduleCohomologyDimension Y.hom B.val n :=
      (moduleCohomologyDimension_eq_of_isIso e Y.hom X.hom he B.val (Iso.refl _) n).symm
    _ = Module.finrank k (moduleCohomology k Y B.val n) :=
      moduleCohomologyDimension_eq_finrank_moduleCohomology Y B.val n
    _ = _ := thetaEvaluationFibre_dimension hX o ho P R (𝟙 (Spec (.of k))) c n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole original Picard classifier specializes to the original
rational coefficient class, with positive degree-g normalization. -/
theorem thetaRationalEvaluation_picardPoint :
    letI := picardCommGrpObj X.hom P R
    picardPoint P R (classOf X.left (thetaRationalEvaluationLineBundle hX o ho P R c)) =
      c ≫ thetaParameterι hX o ho P R ≫ identityComponentι P.obj ≫
        (GrpObj.mulRight (picardPoint P R (coherentGenus k X • classOf X.left
          (PointDivisor.positiveLineBundle X hX o ho)))).hom := by
  let := picardCommGrpObj X.hom P R
  let B := thetaEvaluationFibrePositiveLineBundle hX o ho P R (𝟙 (Spec (.of k))) c
  let e := inv (pullback.fst X.hom (𝟙 (Spec (.of k))))
  have hc : pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))
      (classOf X.left (thetaRationalEvaluationLineBundle hX o ho P R c)) =
      classOf _ (RigidifiedPair.map (c ≫ thetaParameterι hX o ho P R)
        (degreeUniversalPair hX o ho P R (coherentGenus k X))).bundle := by
    change pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))
      (classOf X.left (pullbackLineBundle e B)) = _
    rw [← pullbackClass_classOf, ← pullbackClass_comp, IsIso.hom_inv_id, pullbackClass_id]
    exact thetaEvaluationFibre_degreeUniversalClass hX o ho P R (𝟙 (Spec (.of k))) c
  apply (picardPoint_eq_iff P R _ _).mpr
  have h := degreeUniversalPair_classifies hX o ho P R (coherentGenus k X)
    (T := locallyNoetherianRationalPoint k) (c ≫ thetaParameterι hX o ho P R)
  exact h.symm.trans (congrArg
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
      (op (𝟙_ (Over (Spec (.of k)))))) hc.symm)

end AlgebraicGeometry.Scheme.OverField.Curve
