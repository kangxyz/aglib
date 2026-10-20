/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.ZeroDivisor
public import Aglib.AlgebraicGeometry.Curves.RelativePicard.Fibres
public import Aglib.AlgebraicGeometry.Curves.Abel.Injectivity
public import Aglib.AlgebraicGeometry.Curves.Abel.Morphism
public import Aglib.AlgebraicGeometry.Morphisms.GeometricRetraction
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
# The constructive Abel scheme isomorphism and all-test inverse

An actual representative of a normalized degree-zero class is tensored with
the actual positive origin bundle. Canonical iterated-fibre transport proves
its degree is one on every geometric fibre and its genus is one. General
Riemann–Roch and Noetherian coherent base change then apply to the actual line
bundle on each locally Noetherian test scheme, including nonreduced tests.
The actual evaluation zero divisor has projection an isomorphism, so its
inverse constructs an actual section. The graph ideal comparison proves
that this section recovers the original normalized Picard class.

The same incoming Picard representer now explicitly carries local Noetherianity.
Evaluating class recovery there produces a genuine scheme right inverse.
Independently proved field-point injectivity and the
actual dominant algebraically closed generic point yield the second scheme
identity by reduced/separated extensionality. The resulting actual Abel
isomorphism gives the inverse correspondence on every test scheme, including
nonreduced tests, its naturality, and uniqueness of any section recovering a
given class. Thus representative choices cannot change the recovered section.
No geometric-point bijection is substituted for a scheme identity.
The optional finite-locally-free geometric isomorphism family is not a
parameter: field-point injectivity uses actual nonzero field line-bundle maps.
No inverse or group-law conclusion is a theorem premise. All general source
families are the independently defined incoming families, explicitly listed
in the signatures. The evaluation construction uses locally Noetherian tests;
the final all-test correspondence and naturality follow from the scheme
isomorphism and the full representing equivalence.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated NoetherianSheafCohomologyVanishing
    ProperStructureCohomologyBaseChange)
open AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle PicardGroup classOf classOf_dual classOf_tensor dualLineBundle pullbackClass
    pullbackClass_comp pullbackClass_id pullbackLineBundle tensorLineBundle)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Cohomology
  (evaluationContraction evaluationIdealLineBundle directImageLineBundle)
open AlgebraicGeometry.Scheme.Modules.Hom (zeroInclusion)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom RelativePicard
variable {F : Type u} [Field F] (X : FScheme F)
variable (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
variable (T : FScheme F)
/-- A line-bundle representative of the given Picard class on the pulled-back curve. -/
def representativeLineBundle (a : PicardGroup (pullback X.hom T.hom)) :
    LineBundle (pullback X.hom T.hom) := Quotient.out a
omit [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom] in
@[simp] theorem classOf_representativeLineBundle (a : PicardGroup (pullback X.hom T.hom)) :
    classOf _ (representativeLineBundle X T a) = a := Quotient.out_eq a

/-- The chosen representative tensored with the positive origin bundle,
the dual of the actual origin ideal line bundle. -/
def degreeOneTwist (a : PicardGroup (pullback X.hom T.hom)) :
    LineBundle (pullback X.hom T.hom) :=
  tensorLineBundle _ (representativeLineBundle X T a)
    (dualLineBundle _ (originIdealLineBundle hdivisor X.hom o ho T.hom))

theorem degreeOneTwist_class (a : PicardGroup (pullback X.hom T.hom)) :
    classOf _ (degreeOneTwist X hdivisor o ho T a) =
      a - classOf _ (originIdealLineBundle hdivisor X.hom o ho T.hom) := by
  rw [degreeOneTwist, classOf_tensor, classOf_representativeLineBundle, classOf_dual]
  rfl

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hX : Properties X)
include hbase hcartier in
theorem fibreDegree_originIdeal (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Base F) (t : Over.mk k ⟶ T) :
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K k t
      (classOf _ (originIdealLineBundle hdivisor X.hom o ho T.hom)) = -1 := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom_apply]
  rw [originIdealClass_baseChange hdivisor hbase]
  exact curveDegree_ideal_section hnormal hcomp hreg hclosed hdim hprod hcartier
    (Over.mk (pullback.snd X.hom k)) (curveProperties_baseChange hX K k)
    (graph X.hom k (k ≫ o) (by simp [Category.assoc, ho]))
    (graph_snd X.hom k _ _) (originIdealLineBundle hdivisor X.hom o ho k).property

variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
include hbase hcartier hnorm in
theorem degreeOneTwist_fibre_degree
    (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T)
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ T.left) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod
      (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t))
      (familyFibre_curveProperties X T K t hX)
      (classOf _ (pullbackLineBundle (pullback.fst (pullback.snd X.hom T.hom) t)
        (degreeOneTwist X hdivisor o ho T a.val.val))) = 1 := by
  change curveDegree hnormal hcomp hreg hclosed hdim hprod
    (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t))
    (familyFibre_curveProperties X T K t hX)
    (pullbackClass (pullback.fst (pullback.snd X.hom T.hom) t)
      (classOf _ (degreeOneTwist X hdivisor o ho T a.val.val))) = 1
  rw [familyFibre_degree X T K t hnormal hcomp hreg hclosed hdim hprod hnorm htensor hX,
    degreeOneTwist_class, map_sub, a.property K (t ≫ T.hom) (Over.homMk t rfl),
    fibreDegree_originIdeal X hdivisor o ho T hnormal hcomp hreg hclosed hdim hprod htensor
      hcartier hbase hX]
  norm_num
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom RelativePicard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hgenus : ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hg : coherentGenus F X = 1)
variable (T : FScheme F)
variable (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T)
include hcartier hbase hnorm hgenus hrr hvanish hhigher hg in
theorem degreeOneTwist_profile :
    FibreCohomologyConcentrated (pullback.snd X.hom T.hom)
      (degreeOneTwist X hdivisor o ho T a.val.val).val 1 := by
  apply degreeOneFamily_cohomology hnormal hcomp hreg hclosed hdim hprod
    hrr hvanish hhigher (pullback.snd X.hom T.hom)
    (degreeOneTwist X hdivisor o ho T a.val.val)
    (fun K _ _ t ↦ familyFibre_curveProperties X T K t hX)
  · intro K _ _ t
    exact (familyFibre_genus X T K t hgenus hX).trans hg
  · intro K _ _ t
    exact degreeOneTwist_fibre_degree X hdivisor o ho T hnormal hcomp hreg hclosed hdim hprod
      htensor hcartier hbase hX hnorm a K t

variable [IsLocallyNoetherian T.left]
variable (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
/-- The section obtained from the evaluation zero divisor of the degree-one
twist on a locally Noetherian test scheme. -/
def inverseCandidate : T ⟶ X := by
  letI := hX.proper
  letI := SmoothOfRelativeDimension.smooth 1 X.hom
  letI : SmoothOfRelativeDimension 1 (pullback.snd X.hom T.hom) :=
    MorphismProperty.pullback_snd X.hom T.hom hX.smooth
  let L := degreeOneTwist X hdivisor o ho T a.val.val
  let hL := degreeOneTwist_profile hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX o ho hg T a
  let i := zeroInclusion (evaluationContraction (pullback.snd X.hom T.hom) L hL)
  letI : IsIso (i ≫ pullback.snd X.hom T.hom) :=
    evaluationZero_projection_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase
      hregular hlocal (pullback.snd X.hom T.hom) L hL
      (fun K _ _ t ↦ familyFibre_curveProperties X T K t hX)
      (fun K _ _ t ↦ degreeOneTwist_fibre_degree X hdivisor o ho T
        hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hX hnorm a K t)
  exact Over.homMk (divisorSection X.hom T.hom i) (divisorSection_over X.hom T.hom i)

/-- The evaluation candidate recovers the original normalized degree-zero class
on every locally Noetherian test scheme. -/
theorem inverseCandidate_class :
    degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier hdivisor hbase
      o ho T (inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
        hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal) = a := by
  letI := hX.proper
  letI := SmoothOfRelativeDimension.smooth 1 X.hom
  letI : SmoothOfRelativeDimension 1 (pullback.snd X.hom T.hom) :=
    MorphismProperty.pullback_snd X.hom T.hom hX.smooth
  let f := pullback.snd X.hom T.hom
  let Z := pullback X.hom T.hom
  let a0 : PicardGroup Z := a.val.val
  let s0 := Scheme.RelativePicard.originSection X.hom o ho T
  let L := degreeOneTwist X hdivisor o ho T a0
  let hL := degreeOneTwist_profile hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX o ho hg T a
  let φ := evaluationContraction f L hL
  let i := zeroInclusion φ
  let I := evaluationIdealLineBundle f L hL
  have hφ := evaluationContraction_geometric_regular f L hL hnormal hcomp
    (fun K _ _ t ↦ familyFibre_curveProperties X T K t hX)
  letI : Mono φ := (hregular Z T.left f I φ inferInstance inferInstance hφ).1
  letI : IsIso (i ≫ f) :=
    evaluationZero_projection_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase
      hregular hlocal f L hL
      (fun K _ _ t ↦ familyFibre_curveProperties X T K t hX)
      (fun K _ _ t ↦ degreeOneTwist_fibre_degree X hdivisor o ho T
        hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hX hnorm a K t)
  let s := divisorSection X.hom T.hom i
  let hs := divisorSection_over X.hom T.hom i
  let P := classOf T.left (directImageLineBundle f L hL)
  have hj : classOf Z (graphIdealLineBundle hdivisor X.hom T.hom s hs) =
      classOf Z (zeroIdealLineBundle I φ) := by
    apply Quotient.sound
    exact ⟨divisorGraphIdealIso X.hom T.hom i⟩
  have hc := evaluationZero_class_recovery f L hL
  rw [classOf_dual, ← hj] at hc
  have ht : classOf Z L = a0 - classOf Z (originIdealLineBundle hdivisor X.hom o ho T.hom) :=
    degreeOneTwist_class X hdivisor o ho T a0
  have hb : abelClass hdivisor X.hom o ho T.hom s hs = a0 - pullbackClass f P := by
    rw [abelClass_eq]
    change -classOf Z (graphIdealLineBundle hdivisor X.hom T.hom s hs) +
      classOf Z (originIdealLineBundle hdivisor X.hom o ho T.hom) = _
    calc
      _ = (-classOf Z (graphIdealLineBundle hdivisor X.hom T.hom s hs) + pullbackClass f P) +
          classOf Z (originIdealLineBundle hdivisor X.hom o ho T.hom) - pullbackClass f P := by abel
      _ = classOf Z L + classOf Z (originIdealLineBundle hdivisor X.hom o ho T.hom) -
        pullbackClass f P := by rw [← hc]
      _ = _ := by rw [ht]; abel
  have ha : pullbackClass (s0) a0 = 0 := a.val.property
  have hp : pullbackClass (s0) (pullbackClass f P) = P := by
    rw [← pullbackClass_comp, Scheme.RelativePicard.originSection_snd, pullbackClass_id]
  apply Subtype.ext
  apply Subtype.ext
  change abelClass hdivisor X.hom o ho T.hom s hs -
    pullbackClass f (pullbackClass (s0)
      (abelClass hdivisor X.hom o ho T.hom s hs)) = a0
  have hsub : pullbackClass (s0) (a0 - pullbackClass f P) =
      pullbackClass (s0) a0 -
        pullbackClass (s0) (pullbackClass f P) :=
    map_sub (pullbackHom htensor (s0)) _ _
  rw [hb, hsub, ha, hp, zero_sub, pullbackClass_neg htensor]
  abel
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom RelativePicard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hgenus : ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
variable (hrep : DegreeZeroPicardRepresentability hnormal hcomp hreg hclosed hdim hprod htensor)
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hg : coherentGenus F X = 1)

/-- The evaluation inverse at the same locally Noetherian Picard representer,
applied to the class corresponding to its identity morphism. -/
def abelInverseMorphism :
    representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho ⟶ X :=
  inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
    hnorm hgenus hrr hvanish hhigher X hX o ho hg
    (representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho)
    (((representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
      ho).homEquiv
      (𝟙 _)).toAdd) hregular hlocal

@[reassoc] theorem abelInverseMorphism_comp :
    abelInverseMorphism hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg ≫
    abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier hdivisor hbase o
      ho = 𝟙 _ := by
  apply (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
    ho).homEquiv.injective
  rw [abelMorphism_all_tests]
  dsimp only [abelInverseMorphism]
  rw [inverseCandidate_class]
  rfl

include hnormal hcomp hreg hclosed hdim hprod hcartier hbase hnorm hgenus
  hrr hvanish hhigher hX hg in
theorem abelMorphism_geometric_injective (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Base F) :
    Function.Injective (fun s : Over.mk k ⟶ X ↦ s ≫
      abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier hdivisor hbase
        o ho) := by
  intro s t h
  apply normalizedAbelClass_field_injective hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX o ho hg K k
  have hh := congrArg
    (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
      ho).homEquiv h
  rw [abelMorphism_all_tests, abelMorphism_all_tests] at hh
  exact congrArg (fun a ↦ a.toAdd.val) hh

include hnorm hgenus hrr hvanish hhigher hregular hlocal hg in
theorem abelMorphism_isIso :
    IsIso (abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier hdivisor
      hbase o ho) := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  exact Scheme.Hom.GeometricRetraction.isIso_of_retraction_of_geometric_injective _
    (abelInverseMorphism hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg)
    (abelInverseMorphism_comp hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg)
    (fun K _ _ k ↦
      abelMorphism_geometric_injective hnormal hcomp hreg hclosed hdim hprod htensor hcartier
        hbase hdivisor hnorm hgenus hrr hvanish hhigher hrep X hX o ho hg K k)

/-- The isomorphism whose forward map is the actual Abel morphism, obtained
from its evaluation right inverse and geometric-point injectivity. -/
def abelSchemeIso : X ≅
    representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho := by
  letI := abelMorphism_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
    hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg
  exact asIso (abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier
    hdivisor hbase o ho)

include hrep hnorm hgenus hrr hvanish hhigher hregular hlocal hg in
theorem degreeZeroAbelClass_all_tests_injective (T : FScheme F) :
    Function.Injective (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T) := by
  letI := abelMorphism_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
    hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg
  intro s t h
  apply (cancel_mono (abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX
    hcartier hdivisor hbase o ho)).mp
  apply (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
    ho).homEquiv.injective
  rw [abelMorphism_all_tests, abelMorphism_all_tests, h]

include hrep in
theorem inverseCandidate_abelClass (T : FScheme F) [IsLocallyNoetherian T.left] (s : T ⟶ X) :
    inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher X hX o ho hg T
      (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
        hcartier hdivisor hbase o ho T s) hregular hlocal = s := by
  apply degreeZeroAbelClass_all_tests_injective hnormal hcomp hreg hclosed hdim hprod htensor
    hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T
  exact inverseCandidate_class hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
    hnorm hgenus hrr hvanish hhigher X hX o ho hg T _ hregular hlocal

/-- The actual Abel scheme isomorphism gives the inverse correspondence on
all test schemes, including nonreduced schemes. This inverse uses the full
representing equivalence and the actual scheme inverse. -/
def abelAllTestEquiv (T : FScheme F) : (T ⟶ X) ≃
    degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T := by
  let e := abelSchemeIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg
  let E := representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho
  refine {
    toFun := degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T
    invFun := fun a => E.homEquiv.symm (Multiplicative.ofAdd a) ≫ e.inv
    left_inv := ?_
    right_inv := ?_ }
  · intro t
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    apply E.homEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (abelMorphism_all_tests hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX
      hcartier hdivisor hbase o ho T t).symm
  · intro a
    have h := abelMorphism_all_tests hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX
      hcartier hdivisor hbase o ho T
      (E.homEquiv.symm (Multiplicative.ofAdd a) ≫ e.inv)
    change E.homEquiv ((E.homEquiv.symm (Multiplicative.ofAdd a) ≫ e.inv) ≫ e.hom) =
      Multiplicative.ofAdd (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T
        (E.homEquiv.symm (Multiplicative.ofAdd a) ≫ e.inv)) at h
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, Equiv.apply_symm_apply] at h
    exact congrArg Multiplicative.toAdd h.symm

/-- On a locally Noetherian test scheme, the evaluation construction is the
same section as the inverse supplied by the actual scheme isomorphism. -/
theorem abelAllTestEquiv_symm_eq_inverseCandidate (T : FScheme F)
    [IsLocallyNoetherian T.left]
    (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T) :
    (abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T).symm a =
      inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
        hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal := by
  apply degreeZeroAbelClass_all_tests_injective hnormal hcomp hreg hclosed hdim hprod htensor
    hcartier hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T
  exact ((abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T).apply_symm_apply
        a).trans
    (inverseCandidate_class hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal).symm

include hrep in
/-- Any construction recovering the same class gives the same section. In particular
representative choices cannot change the evaluation-divisor inverse. -/
theorem inverseCandidate_unique (T : FScheme F) [IsLocallyNoetherian T.left]
    (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T)
    (s : T ⟶ X)
    (hs : degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T s = a) :
    s = inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal := by
  apply degreeZeroAbelClass_all_tests_injective hnormal hcomp hreg hclosed hdim hprod htensor
    hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T
  exact hs.trans (inverseCandidate_class hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor
    hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal).symm

omit [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom] in
theorem degreeZeroAbelClass_naturality {T T' : FScheme F} (f : T' ⟶ T) (s : T ⟶ X) :
    degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T' (f ≫ s) =
    degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho f
      (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
        hcartier hdivisor hbase o ho T s) := by
  exact congrArg (fun k ↦ k (ULift.up s))
    ((degreeZeroAbelTransformation hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho).naturality f.op)

/-- The inverse correspondence from the scheme isomorphism is natural on
all test schemes, with no Noetherianity required of either test. -/
theorem abelAllTestEquiv_symm_naturality {T T' : FScheme F} (f : T' ⟶ T)
    (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T) :
    f ≫ (abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T).symm a =
      (abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T').symm
        (degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho f a) := by
  apply (abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T').injective
  rw [Equiv.apply_symm_apply]
  change degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T'
      (f ≫ (abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T).symm a) = _
  rw [degreeZeroAbelClass_naturality]
  exact congrArg (degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho f)
    ((abelAllTestEquiv hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T).apply_symm_apply a)

include hrep in
theorem inverseCandidate_naturality {T T' : FScheme F}
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left] (f : T' ⟶ T)
    (a : degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T) :
    f ≫ inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher X hX o ho hg T a hregular hlocal =
    inverseCandidate hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
      hnorm hgenus hrr hvanish hhigher X hX o ho hg T'
      (degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho f a)
      hregular hlocal := by
  apply inverseCandidate_unique hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase
    hdivisor
    hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o ho hg T'
  rw [degreeZeroAbelClass_naturality, inverseCandidate_class]

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
