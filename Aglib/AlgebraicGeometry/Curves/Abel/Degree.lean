/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.Curves.Abel.Naturality
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Aglib.AlgebraicGeometry.Curves.RelativePicard.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Degree-zero Abel families on every test scheme

Every line bundle on Spec K is proved trivial from its actual local unit
chart, and finiteSchemeDegree is the actual global-sections dimension with
scalars induced by the structural map. The identity Spec K has degree one.

FiniteCartierIdealDegree is a disclosed general derived corollary of Stacks
0AYY and 0AZ3, with 02M0 and 01WX: on a proper integral Noetherian curve with
closed DVR stalks, the actual dual of the kernel ideal of any finite Cartier
closed immersion has degree dim_K Γ(D,O_D). Finiteness of D→Spec K is explicit;
nonreduced divisors and arbitrary fields are allowed. The local ideal/dual
identification, coefficient ord(t)=length(O/(t)), and Euler/residue-weighted
degree reconciliation are retained dependencies of this general family, not
claimed as already proved C lemmas. Primary statements and visible absence
of correction comments inspected 2026-10-09.

The applications are proved: positive rational section degree one, ideal
section degree minus one, graph-difference degree zero, base-pulled classes
have zero geometric-fibre degree, and normalization preserves this. Therefore
the constructed normalized Abel transformation factors through the actual
degree-zero group functor on all test schemes, including nonreduced ones.
No Abel-degree, representing-scheme, or inverse conclusion is assumed.

Other retained families are exactly the inherited B1/C-degree and generic
0B9D/056Q/01CD families named by the imported modules. Application
K2-018#prop:k2018-arithmetic-characters, source
e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open AlgebraicGeometry.Scheme.Hom Divisors

def FiniteCartierIdealDegree : Prop :=
  ∀ (K : Type u) [Field K] (X D : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (p : X ⟶ Spec (.of K)) (i : D ⟶ X) (hdim : topologicalKrullDim X ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X p)
    (hI : Invertible.IsLocallyRankOne X (idealModule i)),
    IsProper p → IsClosedImmersion i → IsFinite (i ≫ p) →
      Picard.Degree.lineBundleDegree X p hdim hprod (Invertible.dualLineBundle X ⟨idealModule i,
        hI⟩) =
        (finiteSchemeDegree K (i ≫ p) : ℤ)

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hcartier : FiniteCartierIdealDegree.{u})
include hcartier

theorem curveDegree_positive_section {K : Type u} [Field K] (Y : FScheme K) (hY : Properties Y)
    (i : Spec (.of K) ⟶ Y.left) (hi : i ≫ Y.hom = 𝟙 _)
    (hI : Invertible.IsLocallyRankOne Y.left (idealModule i)) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod Y hY
      (Invertible.classOf Y.left (Invertible.dualLineBundle Y.left ⟨idealModule i, hI⟩)) = 1 := by
  letI := curveProperties_isIntegral hnormal hcomp hY
  letI := curveProperties_isNoetherian hY
  letI (x : ClosedPoint Y.left) : IsDiscreteValuationRing (Y.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hY x.val x.property
  letI := hY.proper
  haveI : IsClosedImmersion (i ≫ Y.hom) := by rw [hi]; infer_instance
  haveI : IsClosedImmersion i := IsClosedImmersion.of_comp i Y.hom
  haveI : IsFinite (i ≫ Y.hom) := by rw [hi]; infer_instance
  have h := hcartier K Y.left (Spec (.of K)) Y.hom i (le_of_eq (curveProperties_dimension hdim hY))
    (hprod K Y.left Y.hom (curveProperties_dimension hdim hY)) hI inferInstance inferInstance
      inferInstance
  rw [hi, finiteSchemeDegree_id] at h
  exact h

theorem curveDegree_ideal_section {K : Type u} [Field K] (Y : FScheme K) (hY : Properties Y)
    (i : Spec (.of K) ⟶ Y.left) (hi : i ≫ Y.hom = 𝟙 _)
    (hI : Invertible.IsLocallyRankOne Y.left (idealModule i)) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod Y hY
      (Invertible.classOf Y.left ⟨idealModule i, hI⟩) = -1 := by
  have h := curveDegree_positive_section hnormal hcomp hreg hclosed hdim hprod hcartier Y hY i hi hI
  rw [Invertible.classOf_dual, map_neg] at h
  linarith

variable {S X : Scheme.{u}} (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

theorem curveDegree_abelClass {K : Type u} [Field K] (t : Spec (.of K) ⟶ S)
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t))) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd p t)) hY
      (abelClass hdivisor p o ho t s hs) = 0 := by
  have h₁ := curveDegree_ideal_section hnormal hcomp hreg hclosed hdim hprod hcartier
    (Over.mk (pullback.snd p t)) hY (graph p t s hs) (graph_snd p t s hs)
    (graphIdeal_isLocallyRankOne hdivisor p t s hs)
  have h₂ := curveDegree_ideal_section hnormal hcomp hreg hclosed hdim hprod hcartier
    (Over.mk (pullback.snd p t)) hY (graph p t (t ≫ o) (by simp [Category.assoc, ho]))
    (graph_snd p t _ _) (graphIdeal_isLocallyRankOne hdivisor p t _ _)
  rw [abelClass_eq, map_add, map_neg]
  change - curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd p t)) hY
    (Invertible.classOf _ (graphIdealLineBundle hdivisor p t s hs)) +
    curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd p t)) hY
      (Invertible.classOf _ (originIdealLineBundle hdivisor p o ho t)) = 0
  have h₁' : curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd p t)) hY
      (Invertible.classOf _ (graphIdealLineBundle hdivisor p t s hs)) = -1 := h₁
  have h₂' : curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd p t)) hY
      (Invertible.classOf _ (originIdealLineBundle hdivisor p o ho t)) = -1 := h₂
  rw [h₁', h₂']
  norm_num
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open AlgebraicGeometry.Scheme.Hom RelativePicard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)

theorem fibreDegree_basePullback (T : FScheme F) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) (t : Over.mk s ⟶ T) (a : Invertible.PicardGroup T.left) :
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K s t
      (Invertible.pullbackClass (pullback.snd X.hom T.hom) a) = 0 := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom_apply]
  rw [← Invertible.pullbackClass_comp, familyMap_snd, Invertible.pullbackClass_comp,
    fieldPicard_eq_zero K (Invertible.pullbackClass t.left a), Invertible.pullbackClass_zero,
      map_zero]

variable (hcartier : FiniteCartierIdealDegree.{u})
variable (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
section
variable [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
include hcartier hbase in
theorem fibreDegree_abelClass (T : FScheme F) (s : T ⟶ X) (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Base F) (t : Over.mk k ⟶ T) :
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K k t
      (abelClass hdivisor X.hom o ho T.hom s.left (Over.w s)) = 0 := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom_apply]
  rw [abelClass_baseChange hdivisor hbase htensor]
  exact curveDegree_abelClass hnormal hcomp hreg hclosed hdim hprod hcartier hdivisor
    X.hom o ho k (t.left ≫ s.left) (by rw [Category.assoc, Over.w s, Over.w t]; rfl)
      (curveProperties_baseChange hX K k)

include hcartier hbase in
theorem normalizedAbelClass_degree_zero (T : FScheme F) (s : T ⟶ X) :
    normalizedAbelClass hdivisor htensor X.hom o ho T s ∈
      degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T := by
  intro K _ _ k t
  change fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K k t
    (abelClass hdivisor X.hom o ho T.hom s.left (Over.w s) -
      Invertible.pullbackClass (pullback.snd X.hom T.hom)
        (Invertible.pullbackClass (Scheme.RelativePicard.originSection X.hom o ho T)
          (abelClass hdivisor X.hom o ho T.hom s.left (Over.w s)))) = 0
  rw [map_sub, fibreDegree_abelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier
    hdivisor hbase,
    fibreDegree_basePullback, sub_self]
end

def degreeZeroAbelClass (T : FScheme F) (s : T ⟶ X) :
    degreeZeroGroup hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho T := by
  letI := hX.smooth
  letI := hX.proper
  exact ⟨normalizedAbelClass hdivisor htensor X.hom o ho T s,
    normalizedAbelClass_degree_zero hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T s⟩

def degreeZeroAbelTransformation : uliftYoneda.{u+1}.obj X ⟶
    degreeZeroGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho ⋙
      CategoryTheory.forget AddCommGrpCat := by
  letI := hX.smooth
  letI := hX.proper
  refine { app := fun T ↦ ↾(fun s ↦ degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod
    htensor X hX
      hcartier hdivisor hbase o ho T.unop s.down)
           naturality := ?_ }
  intro T T' f
  ext s
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z ↦ z.val) (congrArg (fun k ↦ k s)
    ((normalizedAbelTransformation hdivisor hbase htensor X.hom o ho).naturality f))
end AlgebraicGeometry.Scheme.OverField.Curve.Abel
