/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Reducedness of the original evaluation total space

The actual canonical field fibre is identified with the pullback already
proved reduced. For a field that is not algebraically closed, reducedness
descends from its algebraic closure along the actual scheme-theoretically
dominant flat base change. Thus the original finite flat evaluation map
has geometrically reduced fibres. Its base is the original reduced open
in the same smooth Jacobian, so the original total divisor is reduced.
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal fibre of the original finite flat evaluation map is
reduced at every algebraically closed field test. -/
theorem isReduced_thetaEvaluation_geometricPullback (hg : 0 < coherentGenus k X)
    (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ (thetaParameterOver hX o ho P R).left) :
    IsReduced (pullback (zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
      pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) t) := by
  let b := t ≫ (thetaParameterOver hX o ho P R).hom
  let a : Over.mk b ⟶ thetaParameterOver hX o ho P R := Over.homMk t rfl
  let i := zeroInclusion (thetaEvaluationContraction hX o ho P R)
  let m := (familyScheme X.hom).map a
  let H := isPullback_familyScheme_map X.hom a
  let e := ((IsPullback.of_hasPullback i m).paste_vert H).isoPullback
  have : IsReduced (pullback (C := Scheme.{u}) i m) :=
    isReduced_thetaEvaluationFibre hX o ho P R hg b a
  exact isReduced_of_isOpenImmersion e.inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All original field fibres are geometrically reduced. The passage
from an algebraic closure descends reducedness through actual injective
section maps; it makes no assertion about point cardinalities. -/
theorem geometricallyReduced_thetaEvaluation (hg : 0 < coherentGenus k X) :
    GeometricallyReduced (zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
      pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  let f := zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
    pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  have hf : Flat f := (thetaEvaluation_finite_flat hX o ho P R).2.1
  constructor
  intro K _ t Z u v H
  have : Flat v := MorphismProperty.of_isPullback H hf
  let F := AlgebraicClosure K
  let s : Spec (.of F) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : Surjective s := ⟨fun x => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
  have : IsSchemeTheoreticallyDominant s := IsSchemeTheoreticallyDominant.of_isDominant s
  have : QuasiCompact s := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K F))))
  let e := ((IsPullback.of_hasPullback v s).paste_horiz H).isoPullback
  have : IsReduced (pullback (C := Scheme.{u}) f (s ≫ t)) :=
    isReduced_thetaEvaluation_geometricPullback hX o ho P R hg F (s ≫ t)
  have : IsReduced (pullback (C := Scheme.{u}) v s) := isReduced_of_isOpenImmersion e.hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst v s)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original total evaluation divisor is reduced, by its actual flat
map to the original reduced locally Noetherian open in the same Jacobian. -/
theorem isReduced_thetaEvaluation (hg : 0 < coherentGenus k X) :
    IsReduced (zeroScheme (thetaEvaluationContraction hX o ho P R)) := by
  let := picardCommGrpObj X.hom P R
  have := geometricallyIntegral_identityComponentOver hX P R
  have : IsIntegral (identityComponentOver P.obj).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (identityComponentOver P.obj).hom
  have : IsReduced (thetaParameterOver hX o ho P R).left :=
    isReduced_of_isOpenImmersion (rankOneNonRepeatedOpen hX o ho P R).ι
  have := thetaParameter_isLocallyNoetherian hX o ho P R
  let f := zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
    pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  have : Flat f := (thetaEvaluation_finite_flat hX o ho P R).2.1
  have : GeometricallyReduced f := geometricallyReduced_thetaEvaluation hX o ho P R hg
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry.Scheme.OverField.Curve
