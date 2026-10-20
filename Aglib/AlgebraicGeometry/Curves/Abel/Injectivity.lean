/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSectionUniqueness
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.Abel.Evaluation
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSection
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Aglib.AlgebraicGeometry.Curves.RelativePicard.Fibres
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
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
# Injectivity of the actual Abel class on field-valued points

The actual positive-divisor section is a generator of its direct image in
relative degree one and genus one. This is derived from actual geometric
fibre degree, coherent Riemann–Roch and cohomology/base change over Spec K.
Over Spec K a nonzero map of actual line bundles is invertible directly;
the optional finite-locally-free geometric isomorphism family is not used.

An isomorphism of positive-divisor bundles identifies their canonical
sections up to the pullback of an actual structure-module automorphism.
Literal internal-Hom functoriality and canonical biduality identify the
actual kernel ideals. The native zero-scheme comparison then identifies
sections themselves. Pic(Spec K)=0 removes the origin normalization.
The final injectivity theorem tests every field K and every structural
Spec K → Spec F, not merely a chosen algebraic closure. No inverse,
injectivity, graph uniqueness or group-law conclusion is a premise.
All retained general source families are the previously reviewed incoming
curve, degree, cohomology and Cartier families in the explicit signature.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Incoming HomFunctor d8752f682a16137aba0d5ea899ff1d46a81cddf8b6c72b88525805443bdcf52a;
Bidual 4b38bdec5013bba396fa0f04e0bf9d732107a18af31208e19996c3b01fa537bc;
Uniqueness 089219d061fb4d158a7e3156c93853e8df8b22d5966eb485f61a6500a93c4e45.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated NoetherianSheafCohomologyVanishing
    ProperStructureCohomologyBaseChange)
open AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne classOf dualLineBundle dualSheaf pullbackClass pullbackClass_zero
    pullbackLineBundle )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Cohomology (directImageLineBundle)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom RelativePicard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
variable (T : FScheme F) (s : T ⟶ X)
include hbase hcartier in
theorem fibreDegree_positiveGraph (K : Type u) [Field K] (k : Spec (.of K) ⟶ Base F)
    (t : Over.mk k ⟶ T) :
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K k t
      (classOf _ (positiveGraphLineBundle hdivisor X.hom T.hom s.left (Over.w s))) = 1 := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply, pullbackHom_apply]
  rw [positiveGraphClass_baseChange hdivisor hbase htensor]
  exact curveDegree_positive_section hnormal hcomp hreg hclosed hdim hprod hcartier
    (Over.mk (pullback.snd X.hom k)) (curveProperties_baseChange hX K k)
    (graph X.hom k (t.left ≫ s.left) (by rw [Category.assoc, Over.w s, Over.w t]; rfl))
    (graph_snd X.hom k _ _) (graphIdeal_isLocallyRankOne hdivisor X.hom k _ _)

variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
include htensor hbase hcartier hnorm in
theorem positiveGraph_fibre_degree (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod
      (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t))
      (familyFibre_curveProperties X T K t hX)
      (classOf _ (pullbackLineBundle (pullback.fst (pullback.snd X.hom T.hom) t)
        (positiveGraphLineBundle hdivisor X.hom T.hom s.left (Over.w s)))) = 1 := by
  change curveDegree hnormal hcomp hreg hclosed hdim hprod
    (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t))
    (familyFibre_curveProperties X T K t hX)
    (pullbackClass (pullback.fst (pullback.snd X.hom T.hom) t)
      (classOf _ (positiveGraphLineBundle hdivisor X.hom T.hom s.left (Over.w s)))) = 1
  rw [familyFibre_degree X T K t hnormal hcomp hreg hclosed hdim hprod hnorm htensor hX]
  exact fibreDegree_positiveGraph hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor X hX T s K (t ≫ T.hom) (Over.homMk t rfl)

variable (hgenus : ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable (hg : coherentGenus F X = 1)
include hnormal hcomp hreg hclosed hdim hprod htensor hX
  hbase hcartier hnorm hgenus hrr hvanish hhigher hg in
theorem positiveGraph_profile :
    FibreCohomologyConcentrated (pullback.snd X.hom T.hom)
      (positiveGraphLineBundle hdivisor X.hom T.hom s.left (Over.w s)).val 1 := by
  apply degreeOneFamily_cohomology hnormal hcomp hreg hclosed hdim hprod
    hrr hvanish hhigher (pullback.snd X.hom T.hom)
    (positiveGraphLineBundle hdivisor X.hom T.hom s.left (Over.w s))
    (fun K _ _ t ↦ familyFibre_curveProperties X T K t hX)
  · intro K _ _ t
    exact (familyFibre_genus X T K t hgenus hX).trans hg
  · intro K _ _ t
    exact positiveGraph_fibre_degree hnormal hcomp hreg hclosed hdim hprod htensor hcartier
      hbase hdivisor X hX T s hnorm K t
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
variable (hg : coherentGenus F X = 1) (K : Type u) [Field K]
variable (k : Spec (.of K) ⟶ Base F) (s : Over.mk k ⟶ X)
include hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hnorm
  hgenus hrr hvanish hhigher hX hg in
theorem positiveGraphFieldAdjoint_isIso :
    IsIso (divisorPositiveAdjoint (pullback.snd X.hom k)
      (graph X.hom k s.left (Over.w s))
      (graphIdeal_isLocallyRankOne hdivisor X.hom k s.left (Over.w s))) := by
  letI := hX.proper
  letI := SmoothOfRelativeDimension.smooth 1 X.hom
  haveI : Flat (graph X.hom k s.left (Over.w s) ≫ pullback.snd X.hom k) := by
    rw [graph_snd]; infer_instance
  let L := positiveGraphLineBundle hdivisor X.hom k s.left (Over.w s)
  let hL := positiveGraph_profile hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase
    hdivisor X hX (Over.mk k) s hnorm hgenus hrr hvanish hhigher hg
  let P := directImageLineBundle (pullback.snd X.hom k) L hL
  apply Scheme.Modules.Invertible.fieldLineBundleMap_isIso_of_ne_zero K
    (structureLineBundle (Spec (.of K))) P
    (divisorPositiveAdjoint (pullback.snd X.hom k) (graph X.hom k s.left (Over.w s))
      (graphIdeal_isLocallyRankOne hdivisor X.hom k s.left (Over.w s)))
  letI : IsIntegral (pullback (pullback.snd X.hom k) (𝟙 (Spec (.of K)))) :=
    curveProperties_isIntegral hnormal hcomp
      (familyFibre_curveProperties X (Over.mk k) K (𝟙 (Spec (.of K))) hX)
  intro hz
  apply divisorPositiveAdjoint_fibre_ne_zero (pullback.snd X.hom k)
    (graph X.hom k s.left (Over.w s))
    (graphIdeal_isLocallyRankOne hdivisor X.hom k s.left (Over.w s)) hbase K (𝟙 _)
  rw [hz, Functor.map_zero]
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
include hnormal hcomp hreg hclosed hdim hprod hcartier hbase hnorm hgenus
  hrr hvanish hhigher hX hg in
theorem normalizedAbelClass_field_injective (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Base F) :
    Function.Injective (normalizedAbelClass hdivisor htensor X.hom o ho (Over.mk k)) := by
  intro s t heq
  have hraw := congrArg Subtype.val heq
  change abelClass hdivisor X.hom o ho k s.left (Over.w s) -
      pullbackClass (pullback.snd X.hom k) (pullbackClass
        (Scheme.RelativePicard.originSection X.hom o ho (Over.mk k))
        (abelClass hdivisor X.hom o ho k s.left (Over.w s))) =
    abelClass hdivisor X.hom o ho k t.left (Over.w t) -
      pullbackClass (pullback.snd X.hom k) (pullbackClass
        (Scheme.RelativePicard.originSection X.hom o ho (Over.mk k))
        (abelClass hdivisor X.hom o ho k t.left (Over.w t))) at hraw
  simp only [fieldPicard_eq_zero K, pullbackClass_zero, sub_zero] at hraw
  rw [abelClass_eq, abelClass_eq] at hraw
  have hpos : classOf _ (positiveGraphLineBundle hdivisor X.hom k s.left (Over.w s)) =
      classOf _ (positiveGraphLineBundle hdivisor X.hom k t.left (Over.w t)) :=
    add_right_cancel hraw
  obtain ⟨e⟩ := Quotient.exact hpos
  haveI := positiveGraphFieldAdjoint_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX hg K k s
  haveI := positiveGraphFieldAdjoint_isIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier
    hbase hdivisor hnorm hgenus hrr hvanish hhigher X hX hg K k t
  have hker := kernel_eq_of_positive_iso (pullback.snd X.hom k)
    (graph X.hom k s.left (Over.w s)) (graph X.hom k t.left (Over.w t))
    (graphIdeal_isLocallyRankOne hdivisor X.hom k s.left (Over.w s))
    (graphIdeal_isLocallyRankOne hdivisor X.hom k t.left (Over.w t)) e
  have hgraph := section_eq_of_kernel_eq (pullback.snd X.hom k)
    (graph X.hom k s.left (Over.w s)) (graph X.hom k t.left (Over.w t))
    (graph_snd X.hom k s.left (Over.w s)) (graph_snd X.hom k t.left (Over.w t)) hker
  apply Over.OverMorphism.ext
  simpa only [graph_fst] using congrArg (fun f ↦ f ≫ pullback.fst X.hom k) hgraph
end AlgebraicGeometry.Scheme.OverField.Curve.Abel
