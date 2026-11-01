/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IncidenceGeometry
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RationalNormalization
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.ImageEffectivity
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Actual support comparison for theta incidence

First compute the original difference map on arbitrary scheme tests,
including nonreduced tests. Then identify the original rational evaluation
map with the native product of its two projections. The already proved
rank-one evaluation support and actual proper Abel-image effectivity
criterion give the support comparison at each original rational pair.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open Scheme.Modules.Hom
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily Picard.Degree

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original ambient difference formula holds on ALL scheme tests,
before specialization to rational or closed points. -/
theorem comp_thetaIncidenceDifference :
    letI := picardCommGrpObj X.hom P R
    ∀ {T : Over (Spec (.of k))} (q : T ⟶ X) (c : T ⟶ thetaParameterOver hX o ho P R),
      lift q c ≫ thetaIncidenceDifference hX o ho P R =
        (c ≫ thetaParameterι hX o ho P R) / (q ≫ jacobianCurveMorphism hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  intro T q c
  simp [thetaIncidenceDifference, thetaIncidenceRestrictionMap,
    incidenceDifference_eq, GrpObj.comp_div]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original difference morphism itself is parameter minus the
original Abel curve coordinate. -/
theorem thetaIncidenceDifference_eq :
    letI := picardCommGrpObj X.hom P R
    thetaIncidenceDifference hX o ho P R =
      (snd X (thetaParameterOver hX o ho P R) ≫ thetaParameterι hX o ho P R) /
        (fst X (thetaParameterOver hX o ho P R) ≫ jacobianCurveMorphism hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  simpa only [lift_fst_snd, Category.id_comp] using
    comp_thetaIncidenceDifference hX o ho P R
      (fst X (thetaParameterOver hX o ho P R)) (snd X (thetaParameterOver hX o ho P R))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original rational field-square map has exactly the original
point and parameter as its two projections. -/
theorem thetaRationalFamilyMap_comp_point
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ thetaParameterOver hX o ho P R)
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    q ≫ thetaRationalFamilyMap hX o ho P R c =
      (lift (Over.homMk q hq : 𝟙_ (Over (Spec (.of k))) ⟶ X) c).left := by
  apply pullback.hom_ext
  · simp only [Over.lift_left, pullback.lift_fst]
    change (q ≫ (inv (pullback.fst X.hom (𝟙 (Spec (.of k)))) ≫
      (familyScheme X.hom).map c)) ≫
        pullback.fst X.hom (thetaParameterOver hX o ho P R).hom = q
    rw [Category.assoc, Category.assoc, familyScheme_map_eq_familyMap,
      Hom.familyMap_fst]
    change q ≫ inv (pullback.fst X.hom (𝟙 (Spec (.of k)))) ≫
      pullback.fst X.hom (𝟙 (Spec (.of k))) = q
    rw [IsIso.inv_hom_id, Category.comp_id]
  · simp only [Over.lift_left, pullback.lift_snd]
    rw [Category.assoc, (isPullback_thetaRationalFamilyMap hX o ho P R c).w,
      ← Category.assoc, hq, Category.id_comp]

variable [IsAlgClosed k]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At every original rational pair, the actual evaluation immersion and
the actual restricted theta incidence have the same support. -/
theorem thetaEvaluation_mem_iff_thetaIncidence_mem (hg : 0 < coherentGenus k X)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ thetaParameterOver hX o ho P R)
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    (q ≫ thetaRationalFamilyMap hX o ho P R c) (IsLocalRing.closedPoint k) ∈
      Set.range (zeroInclusion (thetaEvaluationContraction hX o ho P R)) ↔
    (q ≫ thetaRationalFamilyMap hX o ho P R c) (IsLocalRing.closedPoint k) ∈
      Set.range (thetaIncidenceInclusion hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let q0 : 𝟙_ (Over (Spec (.of k))) ⟶ X := Over.homMk q hq
  let a := (c ≫ thetaParameterι hX o ho P R) / (q0 ≫ jacobianCurveMorphism hX o ho P R)
  let L := tensorLineBundle X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
    (PointDivisor.idealLineBundle X hX q hq)
  have heff := mem_basedAbelImage_iff_nonzero_section hX o ho P R
    (coherentGenus k X - 1) L
    (thetaRationalEvaluation_pointTwist_degree hX o ho P R c hg q hq) a
    (thetaRationalEvaluation_pointTwist_normalized_class hX o ho P R hg c q hq)
  have hdiff : (q ≫ thetaRationalFamilyMap hX o ho P R c) ≫
      (thetaIncidenceDifference hX o ho P R).left = a.left := by
    rw [thetaRationalFamilyMap_comp_point hX o ho P R c q hq]
    exact congrArg Over.Hom.left (comp_thetaIncidenceDifference hX o ho P R q0 c)
  have hrange := Scheme.Pullback.Fibre.pullback_range_snd (isPullback_thetaIncidence hX o ho P R)
  rw [hrange]
  change _ ↔ (thetaIncidenceDifference hX o ho P R).left
    ((q ≫ thetaRationalFamilyMap hX o ho P R c) (IsLocalRing.closedPoint k)) ∈
      Set.range (thetaImageInclusion hX o ho P R).left
  have hpoint : (thetaIncidenceDifference hX o ho P R).left
      ((q ≫ thetaRationalFamilyMap hX o ho P R c) (IsLocalRing.closedPoint k)) =
        a.left (IsLocalRing.closedPoint k) :=
    congrArg (fun v => v (IsLocalRing.closedPoint k)) hdiff
  exact (thetaEvaluation_mem_range_iff_nonzero_point_twist hX o ho P R c q hq).trans
    (heff.symm.trans ((congrArg (fun z => z ∈
      Set.range (thetaImageInclusion hX o ho P R).left) hpoint).symm.to_iff))

end AlgebraicGeometry.Scheme.OverField.Curve
