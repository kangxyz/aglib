/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.ProjectiveNormalization
public import Aglib.AlgebraicGeometry.FunctionField.MorphismExt

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.BranchComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`09bd3778c95ee312d11c130086332e1fbc7498f12b9e3bd82fa0fecc1c15830d`.
Only source118–298: normalization into an arbitrary actual proper integral target through its
  displayed critical-cubic affine open, with exact affine pullback and section-origin
  characterization. The original extension input H and actual chart equation/structure map remain
  explicit.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme WeierstrassCurve

section WeierstrassCurve.CriticalCubic.TargetNormalization


/-! Target transport of the explicit normalization through a genuine affine
open chart. The generic extension is constrained by the actual ring map. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
namespace WeierstrassCurve.CriticalCubic.TargetNormalization
universe u
open WeierstrassCurve.CriticalCubic AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k] (a b : k)
local notation "P" => ProjectiveLine.projectiveP1 k
variable {Z : Scheme.{u}} [IsIntegral Z]
  (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
  (j : Spec (.of (equation k a b).toAffine.CoordinateRing) ⟶ Z)
  [hOpen : IsOpenImmersion j]
  (hj : j ≫ sZ = Spec.map (CommRingCat.ofHom
    (algebraMap k (equation k a b).toAffine.CoordinateRing)))
  (H : NormalProperCurveGenericExtension.{u})

omit [IsOpenImmersion j] in
include hj H in
lemma exists_extension :
    ∃ f : P ⟶ Z, f ≫ sZ = ProjectiveLine.structureMap k ∧
      (P).fromSpecStalk (genericPoint P) ≫ f =
        genericParameter k ≫ affineNormalization k a b ≫ j := by
  apply H k P Z (ProjectiveLine.structureMap k) sZ inferInstance
    (parameterProjectiveLine_smooth k) (parameterProjectiveLine_normal k) inferInstance
  rw [Category.assoc, Category.assoc, hj, affineNormalization_over]
  change genericParameter k ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = _
  rw [← ProjectiveLine.chart_over k 0, ← Category.assoc, genericParameter_chart]

/-- The actual extension of the explicit parameter map into the given target. -/
def normalization : P ⟶ Z := (exists_extension k a b sZ j hj H).choose

omit [IsOpenImmersion j] in
@[reassoc] lemma normalization_over : normalization k a b sZ j hj H ≫ sZ =
  ProjectiveLine.structureMap k :=
  (exists_extension k a b sZ j hj H).choose_spec.1

omit [IsOpenImmersion j] in
lemma normalization_generic : (P).fromSpecStalk (genericPoint P) ≫ normalization k a b sZ j hj H =
    genericParameter k ≫ affineNormalization k a b ≫ j :=
  (exists_extension k a b sZ j hj H).choose_spec.2

omit [IsOpenImmersion j] in
@[reassoc] lemma normalization_affine :
    ProjectiveLine.chart k 0 ≫ normalization k a b sZ j hj H = affineNormalization k a b ≫ j := by
  apply ext_of_isDominant_of_isSeparated sZ (ι := genericParameter k)
  · rw [Category.assoc, Category.assoc, normalization_over, hj,
      ProjectiveLine.chart_over, affineNormalization_over]
  · rw [← Category.assoc, genericParameter_chart, normalization_generic]

instance normalization_proper : IsProper (normalization k a b sZ j hj H) := by
  have : IsProper (normalization k a b sZ j hj H ≫ sZ) := by
    rw [normalization_over]
    infer_instance
  exact IsProper.of_comp _ sZ

instance normalization_dominant : IsDominant (normalization k a b sZ j hj H) := by
  let : IsDominant j := AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion j
  have : IsDominant (ProjectiveLine.chart k 0 ≫ normalization k a b sZ j hj H) := by
    rw [normalization_affine]
    infer_instance
  exact IsDominant.of_comp (ProjectiveLine.chart k 0) _

include H in
/-- Birationality of the actual affine normalization follows from its proved
projective generic comparison and the actual two open charts. -/
lemma affineNormalization_functionField_isIso :
    IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (affineNormalization k a
      b))) := by
  let jc := WeierstrassCurve.Projective.affineChart (equation k a b)
  let : IsIntegral (WeierstrassCurve.Projective.scheme (equation k a b)) :=
    WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain _
  let : IsDominant jc := AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion jc
  let : IsDominant (ProjectiveLine.chart k 0) :=
    AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso (ProjectiveLine.chart k 0)
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso jc
  have h : AlgebraicGeometry.Scheme.functionFieldMap
      (ProjectiveLine.chart k 0 ≫ projectiveNormalization k a b H) =
      AlgebraicGeometry.Scheme.functionFieldMap (affineNormalization k a b ≫ jc) := by
    congr 1
    exact projectiveNormalization_affine k a b H
  rw [AlgebraicGeometry.Scheme.functionFieldMap_comp,
    AlgebraicGeometry.Scheme.functionFieldMap_comp] at h
  have hc : IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap jc) ≫
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (affineNormalization k a b)))
        := by
    change IsIso (CommRingCat.ofHom ((AlgebraicGeometry.Scheme.functionFieldMap
      (affineNormalization k a b)).comp (AlgebraicGeometry.Scheme.functionFieldMap jc)))
    rw [← h]
    change IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap
      (projectiveNormalization k a b H)) ≫
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (ProjectiveLine.chart k 0)))
    infer_instance
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap
    jc)) _

instance normalization_functionField_isIso :
    IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (normalization k a b sZ j
      hj H))) := by
  let : IsDominant j := AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant (ProjectiveLine.chart k 0) :=
    AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso (ProjectiveLine.chart k 0)
  let := AlgebraicGeometry.Scheme.FunctionField.fieldMap_isIso j
  let := affineNormalization_functionField_isIso k a b H
  have h : AlgebraicGeometry.Scheme.functionFieldMap
      (ProjectiveLine.chart k 0 ≫ normalization k a b sZ j hj H) =
      AlgebraicGeometry.Scheme.functionFieldMap (affineNormalization k a b ≫ j) := by
    congr 1
    exact normalization_affine k a b sZ j hj H
  rw [AlgebraicGeometry.Scheme.functionFieldMap_comp,
    AlgebraicGeometry.Scheme.functionFieldMap_comp] at h
  have hc : IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap
      (normalization k a b sZ j hj H)) ≫
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (ProjectiveLine.chart k 0))) :=
        by
    change IsIso (CommRingCat.ofHom ((AlgebraicGeometry.Scheme.functionFieldMap
      (ProjectiveLine.chart k 0)).comp (AlgebraicGeometry.Scheme.functionFieldMap
      (normalization k a b sZ j hj H))))
    rw [h]
    change IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap j) ≫
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (affineNormalization k a b)))
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap (ProjectiveLine.chart k 0)))

/-- The exact comparison to the actual inverse image of the affine chart. -/
def affineLift : Spec (.of k[X]) ⟶ pullback (normalization k a b sZ j hj H) j :=
  pullback.lift (ProjectiveLine.chart k 0) (affineNormalization k a b)
    (normalization_affine k a b sZ j hj H)

omit hOpen in
@[reassoc, simp] lemma affineLift_fst
    (k : Type u) [Field k] (a b : k)
    {Z : Scheme.{u}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (j : Spec (.of (equation k a b).toAffine.CoordinateRing) ⟶ Z)
    [IsOpenImmersion j]
    (hj : j ≫ sZ = Spec.map (CommRingCat.ofHom
      (algebraMap k (equation k a b).toAffine.CoordinateRing)))
    (H : NormalProperCurveGenericExtension.{u}) :
    affineLift k a b sZ j hj H ≫ pullback.fst _ _ = ProjectiveLine.chart k 0 := by simp [affineLift]
omit hOpen in
@[reassoc, simp] lemma affineLift_snd
    (k : Type u) [Field k] (a b : k)
    {Z : Scheme.{u}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (j : Spec (.of (equation k a b).toAffine.CoordinateRing) ⟶ Z)
    [IsOpenImmersion j]
    (hj : j ≫ sZ = Spec.map (CommRingCat.ofHom
      (algebraMap k (equation k a b).toAffine.CoordinateRing)))
    (H : NormalProperCurveGenericExtension.{u}) :
    affineLift k a b sZ j hj H ≫ pullback.snd _ _ = affineNormalization k a b := by simp
      [affineLift]

instance affineLift_open : IsOpenImmersion (affineLift k a b sZ j hj H) := by
  have : IsOpenImmersion (affineLift k a b sZ j hj H ≫ pullback.fst _ _) := by
    rw [affineLift_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst _ _)
instance affineLift_proper : IsProper (affineLift k a b sZ j hj H) := by
  have : IsProper (affineLift k a b sZ j hj H ≫ pullback.snd _ _) := by
    rw [affineLift_snd]; infer_instance
  exact IsProper.of_comp _ (pullback.snd _ _)
instance affineLift_dominant : IsDominant (affineLift k a b sZ j hj H) := by
  have : IsDominant (affineLift k a b sZ j hj H ≫ pullback.fst _ _) := by
    rw [affineLift_fst]
    exact AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _
  exact IsDominant.of_comp_of_isOpenImmersion _ (pullback.fst _ _)
instance affineLift_isIso : IsIso (affineLift k a b sZ j hj H) := by
  have : Surjective (affineLift k a b sZ j hj H) :=
    surjective_of_isDominant_of_isClosed_range _ (affineLift k a b sZ j hj
      H).isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

lemma normalization_affine_isPullback :
    IsPullback (ProjectiveLine.chart k 0) (affineNormalization k a b)
      (normalization k a b sZ j hj H) j :=
  IsPullback.of_iso_pullback ⟨normalization_affine k a b sZ j hj H⟩
    (asIso (affineLift k a b sZ j hj H)) (affineLift_fst k a b sZ j hj H)
    (affineLift_snd k a b sZ j hj H)

/-- An actual original-field branch section over the chart's origin gives
an actual original-field tangent root. -/
lemma section_over_origin (p : Spec (.of k) ⟶ P)
    (hp : p ≫ normalization k a b sZ j hj H = originSection k a b ≫ j) :
    ∃ r : k, p = parameterSection k r ≫ ProjectiveLine.chart k 0 ∧ r ^ 2 + a * r - b = 0 := by
  let t := pullback.lift p (originSection k a b) hp ≫ inv (affineLift k a b sZ j hj H)
  have ht : t ≫ affineLift k a b sZ j hj H = pullback.lift p (originSection k a b) hp := by
    simp [t]
  have ht1 : t ≫ ProjectiveLine.chart k 0 = p := by
    rw [← affineLift_fst k a b sZ j hj H, ← Category.assoc, ht]
    simp
  have ht2 : t ≫ affineNormalization k a b = originSection k a b := by
    rw [← affineLift_snd k a b sZ j hj H, ← Category.assoc, ht]
    simp
  obtain ⟨r, htr, hr⟩ := affineSection_over_origin_is_parameter k a b t ht2
  exact ⟨r, (htr ▸ ht1).symm, hr⟩

end WeierstrassCurve.CriticalCubic.TargetNormalization

end -- noncomputable section
end WeierstrassCurve.CriticalCubic.TargetNormalization
