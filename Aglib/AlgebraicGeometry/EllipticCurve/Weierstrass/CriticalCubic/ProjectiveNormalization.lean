/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffineFunctionField
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Integrality
public import Aglib.AlgebraicGeometry.Curves.GenericExtension
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Reciprocal
public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Native extraction from the R5 local-model source
`PointedResolution.CriticalCubic.Projective`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`52a7cdeec355f19079a8fdbbb5d55075947e4349a29f0d57af9958e6db77c58e`.
Actual projective extension of the same affine normalization, function-field comparison, exact
  affine preimage and section-origin characterizations. The original normal/proper curve-extension
  input H remains explicit. The fixed homogeneous P1 and the existing projective Weierstrass
  scheme are reused.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (NormalStalks)

/-!
# Projective extension of the critical cubic normalization, its birational function-field map and
  origin fibre.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section CriticalCubicProjectiveExtension


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial CategoryTheory AlgebraicGeometry
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
open AlgebraicGeometry.Scheme

lemma parameterAffineLine_smooth : SmoothOfRelativeDimension 1 (Spec.algebraMap k k[X]) := by
  unfold Spec.algebraMap
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change (algebraMap k k[X]).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{u+1} k) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k PUnit.{u+1}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u+1})

lemma parameterProjectiveLine_smooth :
    SmoothOfRelativeDimension 1 (ProjectiveLine.structureMap k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (AlgebraicGeometry.Scheme.ProjectiveLine.Reciprocal.chartCover k)
  intro i
  change SmoothOfRelativeDimension 1 (ProjectiveLine.chart k i ≫ ProjectiveLine.structureMap k)
  rw [ProjectiveLine.chart_over]
  exact parameterAffineLine_smooth k

lemma parameterProjectiveLine_normal : NormalStalks (ProjectiveLine.projectiveP1 k) := by
  let := parameterProjectiveLine_smooth k
  exact Scheme.smoothFieldNormality k _ (ProjectiveLine.structureMap k)
    (SmoothOfRelativeDimension.smooth 1 _)

/-- The actual generic point factors through the standard parameter chart. -/
def genericParameter : Spec (ProjectiveLine.projectiveP1 k).functionField ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom
    ((Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k
      0)).symm.toRingHom.comp
      (algebraMap k[X] (FractionRing k[X]))))

lemma genericParameter_chart :
    genericParameter k ≫ ProjectiveLine.chart k 0 =
      (ProjectiveLine.projectiveP1 k).fromSpecStalk (genericPoint (ProjectiveLine.projectiveP1 k))
        := by
  let e := Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k 0)
  have he := Scheme.FunctionField.AffineCompatibility.affine_generic_triangle (.of k[X])
    (ProjectiveLine.chart k 0)
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom
    infer_instance
  apply (cancel_epi (Spec.map (CommRingCat.ofHom e.toRingHom))).mp
  rw [← Category.assoc]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap k[X] (FractionRing k[X])))) ≫
      ProjectiveLine.chart k 0 = _
  rw [← Spec.map_comp_assoc]
  have hcomp : (CommRingCat.ofHom (e.symm.toRingHom.comp
      (algebraMap k[X] (FractionRing k[X]))) ≫ CommRingCat.ofHom e.toRingHom) =
      CommRingCat.ofHom (algebraMap k[X] (FractionRing k[X])) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact e.apply_symm_apply _
  rw [hcomp]
  exact he.symm

instance genericParameter_dominant : IsDominant (genericParameter k) := by
  constructor
  change DenseRange (PrimeSpectrum.comap _)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro z hz
  have hi : Function.Injective
      ((Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k
        0)).symm.toRingHom.comp
        (algebraMap k[X] (FractionRing k[X]))) :=
    (Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k
      0)).symm.injective.comp
      (IsFractionRing.injective k[X] (FractionRing k[X]))
  have hz0 : z = 0 := (map_eq_zero_iff _ hi).mp hz
  rw [hz0]
  exact Ideal.zero_mem _

lemma affineNormalization_over :
    affineNormalization k a b ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (equation k a b).toAffine.CoordinateRing)) =
      Spec.algebraMap k k[X] :=
  Spec.map_algHom_algebraMap (coordinateMap k a b)

local instance criticalProjectiveIntegral : IsIntegral (WeierstrassCurve.Projective.scheme
  (equation k a b)) :=
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain _

/-- A literal generic-point morphism, built from the actual affine normalization. -/
def genericCubicMap : Spec (ProjectiveLine.projectiveP1 k).functionField ⟶
    WeierstrassCurve.Projective.scheme (equation k a b) :=
  genericParameter k ≫ affineNormalization k a b ≫ WeierstrassCurve.Projective.affineChart
    (equation k a b)

lemma genericCubicMap_over :
    genericCubicMap k a b ≫ WeierstrassCurve.Projective.structureMap (equation k a b) =
      (ProjectiveLine.projectiveP1 k).fromSpecStalk (genericPoint (ProjectiveLine.projectiveP1 k)) ≫
        ProjectiveLine.structureMap k := by
  simp only [genericCubicMap, Category.assoc, WeierstrassCurve.Projective.affineChart_structure]
  rw [affineNormalization_over]
  change genericParameter k ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = _
  rw [← ProjectiveLine.chart_over k 0, ← Category.assoc, genericParameter_chart]

lemma exists_projectiveExtension (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    ∃ f : ProjectiveLine.projectiveP1 k ⟶ WeierstrassCurve.Projective.scheme (equation k a b),
      f ≫ WeierstrassCurve.Projective.structureMap (equation k a b) = ProjectiveLine.structureMap
        k ∧
      (ProjectiveLine.projectiveP1 k).fromSpecStalk (genericPoint (ProjectiveLine.projectiveP1 k))
        ≫ f =
        genericCubicMap k a b :=
  H k _ _ (ProjectiveLine.structureMap k) (WeierstrassCurve.Projective.structureMap (equation k a
    b))
    inferInstance (parameterProjectiveLine_smooth k) (parameterProjectiveLine_normal k)
    inferInstance (genericCubicMap k a b) (genericCubicMap_over k a b)

/-- The projective extension uses only the existing universal normal-curve extension family. -/
def projectiveNormalization (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    ProjectiveLine.projectiveP1 k ⟶ WeierstrassCurve.Projective.scheme (equation k a b) :=
  (exists_projectiveExtension k a b H).choose

lemma projectiveNormalization_over (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    projectiveNormalization k a b H ≫ WeierstrassCurve.Projective.structureMap (equation k a b) =
      ProjectiveLine.structureMap k :=
  (exists_projectiveExtension k a b H).choose_spec.1

lemma projectiveNormalization_generic (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    (ProjectiveLine.projectiveP1 k).fromSpecStalk (genericPoint (ProjectiveLine.projectiveP1 k)) ≫
      projectiveNormalization k a b H = genericCubicMap k a b :=
  (exists_projectiveExtension k a b H).choose_spec.2

/-- Separated-target uniqueness proves agreement with the actual affine map. -/
lemma projectiveNormalization_affine (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    ProjectiveLine.chart k 0 ≫ projectiveNormalization k a b H =
      affineNormalization k a b ≫ WeierstrassCurve.Projective.affineChart (equation k a b) := by
  apply ext_of_isDominant_of_isSeparated (WeierstrassCurve.Projective.structureMap (equation k a b))
      (ι := genericParameter k)
  · simp only [Category.assoc, projectiveNormalization_over,
      WeierstrassCurve.Projective.affineChart_structure, ProjectiveLine.chart_over,
      affineNormalization_over]
  · rw [← Category.assoc, genericParameter_chart, projectiveNormalization_generic]
    rfl

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicProjectiveExtension

section CriticalCubicProjectiveBirational


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial CategoryTheory AlgebraicGeometry
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
open AlgebraicGeometry.Scheme
local notation "𝒜" => WeierstrassCurve.Affine.CoordinateRing (WeierstrassCurve.toAffine (equation
  k a b))
local instance : IsIntegral (WeierstrassCurve.Projective.scheme (equation k a b)) :=
  WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain _

instance projectiveNormalization_proper (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    IsProper (projectiveNormalization k a b H) := by
  have : IsProper (projectiveNormalization k a b H ≫
      WeierstrassCurve.Projective.structureMap (equation k a b)) := by
    rw [projectiveNormalization_over]
    infer_instance
  exact IsProper.of_comp _ (WeierstrassCurve.Projective.structureMap (equation k a b))

instance projectiveNormalization_dominant (H :
  Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    IsDominant (projectiveNormalization k a b H) := by
  have : IsDominant (WeierstrassCurve.Projective.affineChart (equation k a b)) :=
    Scheme.isDominant_of_isOpenImmersion _
  have : IsDominant (ProjectiveLine.chart k 0 ≫ projectiveNormalization k a b H) := by
    rw [projectiveNormalization_affine]
    infer_instance
  exact IsDominant.of_comp (ProjectiveLine.chart k 0) _

/-- The field isomorphism furnished by the proved shared fraction field. -/
def normalizationFractionEquiv : FractionRing 𝒜 ≃+* FractionRing k[X] :=
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let := coordinateMap_isFractionRing k a b
  (FractionRing.algEquiv 𝒜 (FractionRing k[X])).toRingEquiv

@[simp] lemma normalizationFractionEquiv_map (z : 𝒜) :
    normalizationFractionEquiv k a b (algebraMap 𝒜 (FractionRing 𝒜) z) =
      algebraMap k[X] (FractionRing k[X]) (coordinateMap k a b z) := by
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let := coordinateMap_isFractionRing k a b
  exact (FractionRing.algEquiv 𝒜 (FractionRing k[X])).commutes z

/-- This equivalence uses the actual standard affine charts on both projective curves. -/
def projectiveFunctionEquiv :
    (WeierstrassCurve.Projective.scheme (equation k a b)).functionField ≃+*
      (ProjectiveLine.projectiveP1 k).functionField :=
  ((Scheme.FunctionField.affineFieldEquiv (.of 𝒜)
      (WeierstrassCurve.Projective.affineChart (equation k a b))).trans
    (normalizationFractionEquiv k a b)).trans
      (Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k 0)).symm

/-- The actual projective map induces exactly the proved field isomorphism. -/
lemma projectiveNormalization_functionFieldMap
    (H : Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    Scheme.functionFieldMap (projectiveNormalization k a b H) =
      (projectiveFunctionEquiv k a b).toRingHom := by
  let eA := Scheme.FunctionField.affineFieldEquiv (.of 𝒜)
    (WeierstrassCurve.Projective.affineChart (equation k a b))
  let eB := Scheme.FunctionField.affineFieldEquiv (.of k[X]) (ProjectiveLine.chart k 0)
  have hc : eB.toRingHom.comp ((Scheme.functionFieldMap
      (projectiveNormalization k a b H)).comp eA.symm.toRingHom) =
      (normalizationFractionEquiv k a b).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝒜)
    intro z
    change eB (Scheme.functionFieldMap (projectiveNormalization k a b H)
      (eA.symm (algebraMap 𝒜 (FractionRing 𝒜) z))) =
      normalizationFractionEquiv k a b (algebraMap 𝒜 (FractionRing 𝒜) z)
    rw [normalizationFractionEquiv_map]
    exact Scheme.FunctionField.AffineCompatibility.affineFieldEquiv_map_coordinate (.of k[X]) (.of
      𝒜)
      (projectiveNormalization k a b H) (ProjectiveLine.chart k 0)
      (WeierstrassCurve.Projective.affineChart (equation k a b))
      (CommRingCat.ofHom (coordinateMap k a b).toRingHom)
      (projectiveNormalization_affine k a b H) z
  apply RingHom.ext
  intro z
  apply eB.injective
  have h := DFunLike.congr_fun hc (eA z)
  simpa [projectiveFunctionEquiv, eA, eB, RingHom.comp_apply] using h

instance projectiveNormalization_functionField_isIso
    (H : Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u}) :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap
      (projectiveNormalization k a b H))) := by
  rw [projectiveNormalization_functionFieldMap]
  change IsIso (projectiveFunctionEquiv k a b).toCommRingCatIso.hom
  infer_instance

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicProjectiveBirational

section CriticalCubicAffinePullback


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
open AlgebraicGeometry.Scheme
variable (H : Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})

/-- The actual comparison with the preimage of the cubic's affine chart. -/
def affinePullbackLift : Spec (.of k[X]) ⟶
    pullback (projectiveNormalization k a b H) (WeierstrassCurve.Projective.affineChart (equation
      k a b)) :=
  pullback.lift (ProjectiveLine.chart k 0) (affineNormalization k a b)
    (projectiveNormalization_affine k a b H)

@[reassoc, simp] lemma affinePullbackLift_fst :
    affinePullbackLift k a b H ≫ pullback.fst _ _ = ProjectiveLine.chart k 0 := by
  simp [affinePullbackLift]

@[reassoc, simp] lemma affinePullbackLift_snd :
    affinePullbackLift k a b H ≫ pullback.snd _ _ = affineNormalization k a b := by
  simp [affinePullbackLift]

instance affinePullbackLift_open : IsOpenImmersion (affinePullbackLift k a b H) := by
  have : IsOpenImmersion (affinePullbackLift k a b H ≫ pullback.fst _ _) := by
    rw [affinePullbackLift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst _ _)

instance affinePullbackLift_proper : IsProper (affinePullbackLift k a b H) := by
  have : IsProper (affinePullbackLift k a b H ≫ pullback.snd _ _) := by
    rw [affinePullbackLift_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd _ _)

instance affinePullbackLift_dominant : IsDominant (affinePullbackLift k a b H) := by
  have : IsDominant (affinePullbackLift k a b H ≫ pullback.fst _ _) := by
    rw [affinePullbackLift_fst]
    exact Scheme.isDominant_of_isOpenImmersion _
  exact IsDominant.of_comp_of_isOpenImmersion _ (pullback.fst _ _)

/-- Properness of the finite affine normalization rules out extra points over the affine chart. -/
instance affinePullbackLift_isIso : IsIso (affinePullbackLift k a b H) := by
  have : Surjective (affinePullbackLift k a b H) :=
    surjective_of_isDominant_of_isClosed_range _
      (affinePullbackLift k a b H).isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- The affine parameter line identified with the preimage of the cubic's affine chart. -/
def affinePullbackIso : Spec (.of k[X]) ≅
    pullback (projectiveNormalization k a b H) (WeierstrassCurve.Projective.affineChart (equation
      k a b)) :=
  asIso (affinePullbackLift k a b H)

lemma projectiveNormalization_affine_isPullback :
    IsPullback (ProjectiveLine.chart k 0) (affineNormalization k a b)
      (projectiveNormalization k a b H) (WeierstrassCurve.Projective.affineChart (equation k a b))
        := by
  exact IsPullback.of_iso_pullback ⟨projectiveNormalization_affine k a b H⟩
    (affinePullbackIso k a b H) (affinePullbackLift_fst k a b H) (affinePullbackLift_snd k a b H)

/-- Every scheme-valued point over the affine target has a unique affine parameter lift. -/
lemma projectiveNormalization_affine_lift {T : Scheme.{u}}
    (p : T ⟶ ProjectiveLine.projectiveP1 k)
    (q : T ⟶ Spec (.of (equation k a b).toAffine.CoordinateRing))
    (hpq : p ≫ projectiveNormalization k a b H = q ≫ WeierstrassCurve.Projective.affineChart
      (equation k a b)) :
    ∃! t : T ⟶ Spec (.of k[X]),
      t ≫ ProjectiveLine.chart k 0 = p ∧ t ≫ affineNormalization k a b = q := by
  let t := pullback.lift p q hpq ≫ (affinePullbackIso k a b H).inv
  have ht : t ≫ affinePullbackLift k a b H = pullback.lift p q hpq := by
    simp [t, affinePullbackIso]
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · rw [← affinePullbackLift_fst k a b H, ← Category.assoc, ht]
    simp
  · rw [← affinePullbackLift_snd k a b H, ← Category.assoc, ht]
    simp
  · intro t' ht'
    apply (cancel_mono (ProjectiveLine.chart k 0)).mp
    exact ht'.1.trans (by
      rw [← affinePullbackLift_fst k a b H, ← Category.assoc, ht]
      simp)

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicAffinePullback

section CriticalCubicProjectiveFibre


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial CategoryTheory AlgebraicGeometry
namespace WeierstrassCurve.CriticalCubic
variable (k : Type u) [Field k] (a b : k)
open AlgebraicGeometry.Scheme
variable (H : Scheme.FunctionField.GenericExtension.NormalProperCurveGenericExtension.{u})

lemma affineSection_over_origin_is_parameter
    (t : Spec (.of k) ⟶ Spec (.of k[X]))
    (ht : t ≫ affineNormalization k a b = originSection k a b) :
    ∃ r : k, t = parameterSection k r ∧ r ^ 2 + a * r - b = 0 := by
  let f : k[X] →+* k := (Spec.preimage t).hom
  have hf : Spec.map (CommRingCat.ofHom f) = t := Spec.map_preimage t
  have hh := ht
  rw [← hf, affineNormalization, originSection, ← Spec.map_comp] at hh
  have hhom := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
  have hc (c : k) : f (C c) = c := by
    have h := DFunLike.congr_fun hhom (algebraMap k (equation k a b).toAffine.CoordinateRing c)
    change f (coordinateMap k a b (algebraMap k _ c)) = originMap k a b (algebraMap k _ c) at h
    simpa using h
  let r := f X
  have heval : (aeval r).toRingHom = f := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa using (hc c).symm
    · simp [r]
  have ht' : t = parameterSection k r := by
    rw [← hf, parameterSection, heval]
  refine ⟨r, ht', ?_⟩
  apply (parameterSection_comp_eq_origin_iff k a b r).mp
  rwa [ht'] at ht

/-- The full rational fibre of the actual projective map lies in the parameter chart,
and is exactly the zero set of the tangent polynomial. -/
lemma projectiveSection_origin_iff
    (p : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) :
    p ≫ projectiveNormalization k a b H =
        originSection k a b ≫ WeierstrassCurve.Projective.affineChart (equation k a b) ↔
      ∃ r : k, p = parameterSection k r ≫ ProjectiveLine.chart k 0 ∧
        r ^ 2 + a * r - b = 0 := by
  constructor
  · intro hp
    obtain ⟨t, ht, -⟩ := projectiveNormalization_affine_lift k a b H p (originSection k a b) hp
    obtain ⟨r, rfl, hr⟩ := affineSection_over_origin_is_parameter k a b t ht.2
    exact ⟨r, ht.1.symm, hr⟩
  · rintro ⟨r, rfl, hr⟩
    rw [Category.assoc, projectiveNormalization_affine, ← Category.assoc,
      (parameterSection_comp_eq_origin_iff k a b r).mpr hr]

/-- Two distinct actual projective preimages imply an ordinary-node tangent discriminant.
The roots are extracted from actual morphisms, with no chosen branch count input. -/
lemma two_projectiveSections_discriminant_ne_zero
    (p q : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k) (hpq : p ≠ q)
    (hp : p ≫ projectiveNormalization k a b H =
      originSection k a b ≫ WeierstrassCurve.Projective.affineChart (equation k a b))
    (hq : q ≫ projectiveNormalization k a b H =
      originSection k a b ≫ WeierstrassCurve.Projective.affineChart (equation k a b)) :
    a ^ 2 + 4 * b ≠ 0 := by
  obtain ⟨r, rfl, hr⟩ := (projectiveSection_origin_iff k a b H p).mp hp
  obtain ⟨s, rfl, hs⟩ := (projectiveSection_origin_iff k a b H q).mp hq
  exact two_roots_discriminant_ne_zero k a b r s (fun h => hpq (by rw [h])) hr hs

end WeierstrassCurve.CriticalCubic

end
end CriticalCubicProjectiveFibre
