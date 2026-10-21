/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedComparisonTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedComparisonNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange

/-!
# Naturality of the actual finite-coefficient étale H¹ comparison

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Scheme variance uses actual
small-étale inverse image and the actual induced fibre-group homomorphism.
Coefficient variance uses actual group/sheaf maps and literal fibre markings.
The finite-universe transports act on the existing common cocycle quotient.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Naturality
open GroupCohomology.ContinuousH1 MarkedCoefficients

section CoefficientTransport
variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B₀ B D₀ D : Type*}
variable [AddCommGroup B₀] [AddCommGroup B] [AddCommGroup D₀] [AddCommGroup D]
variable [TopologicalSpace B₀] [DiscreteTopology B₀] [TopologicalSpace B] [DiscreteTopology B]
variable [TopologicalSpace D₀] [DiscreteTopology D₀] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B₀] [ContinuousSMul G B₀] [DistribMulAction G B] [ContinuousSMul G B]
variable [DistribMulAction H D₀] [ContinuousSMul H D₀] [DistribMulAction H D] [ContinuousSMul H D]
variable (φ : ContinuousMonoidHom H G)
variable (e : B₀ ≃+ B) (he : ∀ (g : G) b, e (g • b) = g • e b)
variable (d : D₀ ≃+ D) (hd : ∀ (h : H) a, d (h • a) = h • d a)
variable (q : PullbackMap (A := B) (B := D) φ)

/-- The actual marked coefficient map between small point modules is the
explicit composite d⁻¹ ∘ q ∘ e; its relative equivariance is proved. -/
def transportedPullbackMap : PullbackMap (A := B₀) (B := D₀) φ where
  toFun b := d.symm (q (e b))
  map_zero' := by
    change d.symm (q (e 0)) = 0
    rw [e.map_zero]
    exact (congrArg d.symm q.toAddMonoidHom.map_zero).trans d.symm.map_zero
  map_add' a b := by simp only [map_add, q.map_add]
  continuous_toFun := continuous_of_discreteTopology
  map_smul' h b := by
    rw [he, q.map_smul]
    exact coefficientEquiv_symm_equivariant d hd h _

/-- Marking/universe transport commutes with simultaneous group restriction
and coefficient change on the one common continuous H¹ quotient. -/
theorem coefficientH1Equiv_pullback (a : H1 G B₀) :
    coefficientH1Equiv d hd ((transportedPullbackMap φ e he d hd q).onH1 a) =
      q.onH1 (coefficientH1Equiv e he a) := by
  obtain ⟨c, rfl⟩ := classOf_surjective G B₀ a
  rw [PullbackMap.onH1_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, PullbackMap.onH1_classOf]
  congr 1
  apply Cocycle.ext
  intro h
  exact d.apply_symm_apply _

end CoefficientTransport

section OrdinaryCoefficientTransport
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {B₀ B D₀ D : Type*}
variable [AddCommGroup B₀] [AddCommGroup B] [AddCommGroup D₀] [AddCommGroup D]
variable [TopologicalSpace B₀] [DiscreteTopology B₀] [TopologicalSpace B] [DiscreteTopology B]
variable [TopologicalSpace D₀] [DiscreteTopology D₀] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B₀] [ContinuousSMul G B₀] [DistribMulAction G B] [ContinuousSMul G B]
variable [DistribMulAction G D₀] [ContinuousSMul G D₀] [DistribMulAction G D] [ContinuousSMul G D]
variable (e : B₀ ≃+ B) (he : ∀ (g : G) b, e (g • b) = g • e b)
variable (d : D₀ ≃+ D) (hd : ∀ (g : G) a, d (g • a) = g • d a)
variable (q : CoefficientMap G B D)

/-- The explicit marked coefficient map on actual small point modules. -/
def transportedCoefficientMap : CoefficientMap G B₀ D₀ :=
  (coefficientMapOfEquiv d.symm (coefficientEquiv_symm_equivariant d hd)).comp
    (q.comp (coefficientMapOfEquiv e he))

/-- Ordinary coefficient change commutes with finite marking/universe transport
on the existing common continuous cohomology quotient. -/
theorem coefficientH1Equiv_coefficient (a : H1 G B₀) :
    coefficientH1Equiv d hd ((transportedCoefficientMap e he d hd q).onH1 a) =
      q.onH1 (coefficientH1Equiv e he a) := by
  obtain ⟨c, rfl⟩ := classOf_surjective G B₀ a
  rw [CoefficientMap.onH1_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, CoefficientMap.onH1_classOf]
  congr 1
  apply Cocycle.ext
  intro g
  exact d.apply_symm_apply _

end OrdinaryCoefficientTransport

section RestrictionTransport
variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B D : Type*} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction G D] [ContinuousSMul G D]
variable (φ : ContinuousMonoidHom H G)
variable (e : B ≃+ D) (he : ∀ (g : G) b, e (g • b) = g • e b)

/-- Restriction along the actual group homomorphism commutes with the proved
coefficient marking transport, including different coefficient universes. -/
theorem restriction_coefficientH1Equiv (a : H1 G B) :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    letI := restrictedAction D φ
    letI := restrictedAction_continuous D φ
    coefficientH1Equiv e (fun h b => he (φ h) b) (restriction B φ a) =
      restriction D φ (coefficientH1Equiv e he a) := by
  let := restrictedAction B φ
  let := restrictedAction_continuous B φ
  let := restrictedAction D φ
  let := restrictedAction_continuous D φ
  obtain ⟨c, rfl⟩ := classOf_surjective G B a
  rw [restriction_classOf, coefficientH1Equiv_classOf,
    coefficientH1Equiv_classOf, restriction_classOf]
  congr 1

end RestrictionTransport
section RelativeCoefficient
variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {B D : Type*} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction H D] [ContinuousSMul H D]
variable (φ : ContinuousMonoidHom H G) (q : PullbackMap (A := B) (B := D) φ)

/-- A relative coefficient map is an ordinary coefficient map after the
explicit restricted action, with no action identification assumed. -/
def pullbackCoefficientMap :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    CoefficientMap H B D := by
  letI := restrictedAction B φ
  letI := restrictedAction_continuous B φ
  exact { q.toContinuousAddMonoidHom with map_smul' := q.map_smul }

/-- The two-step restriction/coefficient map is the existing single combined
PullbackMap on the same common cohomology quotient. -/
theorem pullbackCoefficientMap_restriction (a : H1 G B) :
    letI := restrictedAction B φ
    letI := restrictedAction_continuous B φ
    (pullbackCoefficientMap φ q).onH1 (restriction B φ a) = q.onH1 a := by
  let := restrictedAction B φ
  let := restrictedAction_continuous B φ
  obtain ⟨c, rfl⟩ := classOf_surjective G B a
  rw [restriction_classOf, CoefficientMap.onH1_classOf, PullbackMap.onH1_classOf]
  rfl

end RelativeCoefficient
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality
open CategoryTheory
open FundamentalGroupComparison SchemeTorsorClassification SchemeTorsorBaseChange
universe u v v' w w'
attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian hasSheafifyLarge

section ActualCoefficients
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (A B : Grp (Over X)) [IsCommMonObj A.X] [IsCommMonObj B.X]
variable [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Finite M] [Finite N] [TopologicalSpace M] [TopologicalSpace N]
variable [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markA : (Over.mk s ⟶ A.X) ≃* Multiplicative M)
variable (markB : (Over.mk s ⟶ B.X) ≃* Multiplicative N)
variable (hmarkA : ∀ (γ : FiberAutGroup s) a,
  markA (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (markA a).toAdd))
variable (hmarkB : ∀ (γ : FiberAutGroup s) a,
  markB (γ.hom.app (coefficientCover B) a) = Multiplicative.ofAdd (γ • (markB a).toAdd))
variable (hcoeffA : FiniteCoefficient (representedSheaf A))
variable (hcoeffB : FiniteCoefficient (representedSheaf B))

/-- Actual coefficient morphisms commute with the actual Ext/common-H¹
comparison. The marked map is an ordinary equivariant additive map, and
its only compatibility premise is its effect on genuine coefficient points. -/
theorem representedH1AddEquiv_coefficient_small (q : A ⟶ B)
    (ψ : CoefficientMap (FiberAutGroup s) M N)
    (hq : ∀ a : Over.mk s ⟶ A.X, (markB (a ≫ q.hom.hom)).toAdd = ψ (markA a).toAdd)
    (a : H1Etale X (representedSheaf A)) :
    representedH1AddEquiv s B hA hR N markB hmarkB hcoeffB
      (coefficientMap (representedSheafMap q) a) =
      ψ.onH1 (representedH1AddEquiv s A hA hR M markA hmarkA hcoeffA a) := by
  obtain ⟨p, rfl⟩ := (hA.bijective (representedSheaf A)).surjective a
  refine Quotient.inductionOn p ?_
  intro P
  change representedH1AddEquiv s B hA hR N markB hmarkB hcoeffB
    (coefficientMap (representedSheafMap q) (torsorExtClass P)) =
    ψ.onH1 (representedH1AddEquiv s A hA hR M markA hmarkA hcoeffA (torsorExtClass P))
  rw [← torsorExtClass_pushout P (representedSheafMap q),
    representedH1AddEquiv_torsor, representedH1AddEquiv_torsor]
  exact representedTorsorClass_naturality A B q (torsorPushoutMap P (representedSheafMap q))
    s markA markB hmarkA hmarkB ψ hq hR hcoeffA.locally_constant hcoeffB.locally_constant

end ActualCoefficients

section UniverseCoefficients
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (A B : Grp (Over X)) [IsCommMonObj A.X] [IsCommMonObj B.X]
variable [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N]
variable [Finite M] [Finite N] [TopologicalSpace M] [TopologicalSpace N]
variable [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markA : (Over.mk s ⟶ A.X) ≃* Multiplicative M)
variable (markB : (Over.mk s ⟶ B.X) ≃* Multiplicative N)
variable (hmarkA : ∀ (γ : FiberAutGroup s) a,
  markA (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (markA a).toAdd))
variable (hmarkB : ∀ (γ : FiberAutGroup s) a,
  markB (γ.hom.app (coefficientCover B) a) = Multiplicative.ofAdd (γ • (markB a).toAdd))
variable (hcoeffA : FiniteCoefficient (representedSheaf A))
variable (hcoeffB : FiniteCoefficient (representedSheaf B))

/-- Actual coefficient morphisms commute with the actual Ext/common-H¹
comparison. The marked map is an ordinary equivariant additive map, and
its only compatibility premise is its effect on genuine coefficient points. -/
theorem representedH1AddEquiv_coefficient (q : A ⟶ B)
    (ψ : CoefficientMap (FiberAutGroup s) M N)
    (hq : ∀ a : Over.mk s ⟶ A.X, (markB (a ≫ q.hom.hom)).toAdd = ψ (markA a).toAdd)
    (a : H1Etale X (representedSheaf A)) :
    representedH1AddEquiv s B hA hR N markB hmarkB hcoeffB
      (coefficientMap (representedSheafMap q) a) =
      ψ.onH1 (representedH1AddEquiv s A hA hR M markA hmarkA hcoeffA a) := by
  let := pointModuleAction s A M markA
  let := pointModuleContinuousSMul s A M markA
  let := pointModuleAction s B N markB
  let := pointModuleContinuousSMul s B N markB
  let e := pointModuleEquiv s A M markA
  let d := pointModuleEquiv s B N markB
  have he := pointModuleEquiv_equivariant s A M markA
  have hd := pointModuleEquiv_equivariant s B N markB
  let ψ₀ := transportedCoefficientMap e he d hd ψ
  have hq₀ : ∀ b : Over.mk s ⟶ A.X,
      (pointModuleMark s B (b ≫ q.hom.hom)).toAdd = ψ₀ (pointModuleMark s A b).toAdd := by
    intro b
    apply d.injective
    change (markB (b ≫ q.hom.hom)).toAdd = d (d.symm (ψ (markA b).toAdd))
    rw [d.apply_symm_apply]
    exact hq b
  rw [MarkedComparisonTransport.representedH1AddEquiv_marking s B (PointModule s B) N
    (pointModuleMark s B) markB (pointModuleMark_equivariant s B N markB hmarkB) hmarkB
    d hd (fun _ => rfl) hA hR hcoeffB,
    MarkedComparisonTransport.representedH1AddEquiv_marking s A (PointModule s A) M
    (pointModuleMark s A) markA (pointModuleMark_equivariant s A M markA hmarkA) hmarkA
    e he (fun _ => rfl) hA hR hcoeffA,
    representedH1AddEquiv_coefficient_small s A B hA hR (PointModule s A) (PointModule s B)
    (pointModuleMark s A) (pointModuleMark s B)
    (pointModuleMark_equivariant s A M markA hmarkA)
    (pointModuleMark_equivariant s B N markB hmarkB) hcoeffA hcoeffB q ψ₀ hq₀]
  exact coefficientH1Equiv_coefficient e he d hd ψ _

end UniverseCoefficients

/-- Canonical actual pullback marking, allowing the marked module in any universe. -/
-- Keep the original commutative finite-etale coefficient-group inputs of this marking.
@[nolint unusedArguments]
def canonicalPullbackFiberMark {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
    (s : Spec (CommRingCat.of K) ⟶ S) {M : Type v} [AddCommGroup M]
    (mark : (Over.mk (s ≫ f) ⟶ A.X) ≃* Multiplicative M) :=
  MarkedComparisonTransport.pullbackFiberMark f s A M mark

/-- The actual canonical marking has precisely the restricted monodromy. -/
theorem canonicalPullbackFiberMark_equivariant {X S : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
    (s : Spec (CommRingCat.of K) ⟶ S) {M : Type v} [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (FiberAutGroup (s ≫ f)) M] [ContinuousSMul (FiberAutGroup (s ≫ f)) M]
    (mark : (Over.mk (s ≫ f) ⟶ A.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup (s ≫ f)) a,
      mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd)) :
    letI := restrictedAction M (inducedGroupHom f s)
    ∀ (γ : FiberAutGroup s) a,
      canonicalPullbackFiberMark f A s mark (γ.hom.app (coefficientCover (baseChangedGroup f A))
        a) =
        Multiplicative.ofAdd (γ • (canonicalPullbackFiberMark f A s mark a).toAdd) :=
  MarkedComparisonTransport.pullbackFiberMark_equivariant f s A M mark hmark

section ActualSchemePullback
variable {X S : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (s ≫ f))]
variable [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [PreconnectedSpace S]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
variable (hAX : Stacks03AJ.{u, w} X) (hAS : Stacks03AJ.{u, w'} S)
variable (hRX : Stacks03RV X) (hRS : Stacks03RV S)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (s ≫ f)) M] [ContinuousSMul (FiberAutGroup (s ≫ f)) M]
variable (mark : (Over.mk (s ≫ f) ⟶ A.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup (s ≫ f)) a,
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf A))

/-- The required finite coefficient scope on the pulled-back actual group
scheme is constructed from the original scope, with the same positive level. -/
def pulledBackFiniteCoefficient : FiniteCoefficient (representedSheaf (baseChangedGroup f A)) :=
  (hcoeff.pullback f).ofIso (representedSheafBaseChangeIso f A).symm

/-- Actual scheme inverse image agrees with restriction along the actual
continuous fibre-group map, using the canonical group and sheaf fibre transports. -/
theorem representedH1AddEquiv_pullback (a : H1Etale X (representedSheaf A)) :
    letI := restrictedAction M (inducedGroupHom f s)
    letI := restrictedAction_continuous M (inducedGroupHom f s)
    representedH1AddEquiv s (baseChangedGroup f A) hAS hRS M
      (canonicalPullbackFiberMark f A s mark) (canonicalPullbackFiberMark_equivariant f A s mark
        hmark)
      (pulledBackFiniteCoefficient f A hcoeff)
      (coefficientMap (representedSheafBaseChangeIso f A).hom (h1Pullback f (representedSheaf A)
        a)) =
      restriction M (inducedGroupHom f s)
        (representedH1AddEquiv (s ≫ f) A hAX hRX M mark hmark hcoeff a) := by
  let := restrictedAction M (inducedGroupHom f s)
  let := restrictedAction_continuous M (inducedGroupHom f s)
  obtain ⟨p, rfl⟩ := (hAX.bijective (representedSheaf A)).surjective a
  refine Quotient.inductionOn p ?_
  intro P
  let Y := P.finiteEtaleRepresentative hRX hcoeff.locally_constant
  let e := P.finiteEtaleRepresentativeIso hRX hcoeff.locally_constant
  let τ := P.representedSchemeAction A Y e
  let : Surjective Y.obj.hom := P.represented_surjective A Y e
  have he : torsorExtClass (torsorOfSchemeAction A Y τ) = torsorExtClass P :=
    torsorExtClass_iso (P.representedSchemeActionIso A Y e)
  change representedH1AddEquiv s (baseChangedGroup f A) hAS hRS M _ _ _
    (coefficientMap (representedSheafBaseChangeIso f A).hom
      (h1Pullback f (representedSheaf A) (torsorExtClass P))) =
    restriction M (inducedGroupHom f s)
      (representedH1AddEquiv (s ≫ f) A hAX hRX M mark hmark hcoeff (torsorExtClass P))
  rw [← he, torsorExtClass_pullbackSchemeAction]
  let : Nonempty (Fiber (s ≫ f) Y) := nonempty_fiber_of_surjective (s ≫ f) Y
  let t : Fiber (s ≫ f) Y := Classical.choice inferInstance
  rw [MarkedComparisonTransport.representedH1AddEquiv_schemeAction s (baseChangedGroup f A)
    M (canonicalPullbackFiberMark f A s mark) (canonicalPullbackFiberMark_equivariant f A s mark
      hmark)
    hAS hRS (pulledBackFiniteCoefficient f A hcoeff) ((baseChange f).obj Y)
    (pullbackSchemeAction f A Y τ) (fiberBaseChangeEquiv f s Y t),
    MarkedComparisonTransport.representedH1AddEquiv_schemeAction (s ≫ f) A M mark hmark
    hAX hRX hcoeff Y τ t, restriction_classOf]
  congr 1
  exact MarkedComparisonTransport.markedBasedCocycle_pullback f s A M mark hmark Y τ t

/-- The comparison on the literal inverse-image coefficient sheaf, rather
than only its represented-sheaf presentation. -/
def inverseImageH1AddEquiv :
    letI := restrictedAction M (inducedGroupHom f s)
    letI := restrictedAction_continuous M (inducedGroupHom f s)
    H1Etale S ((inverseImage f).obj (representedSheaf A)) ≃+ H1 (FiberAutGroup s) M := by
  letI := restrictedAction M (inducedGroupHom f s)
  letI := restrictedAction_continuous M (inducedGroupHom f s)
  exact (coefficientIso (representedSheafBaseChangeIso f A)).trans
    (representedH1AddEquiv s (baseChangedGroup f A) hAS hRS M
      (canonicalPullbackFiberMark f A s mark) (canonicalPullbackFiberMark_equivariant f A s mark
        hmark)
      (pulledBackFiniteCoefficient f A hcoeff))

/-- Literal inverse-image H¹ comparison satisfies the actual scheme square. -/
theorem inverseImageH1AddEquiv_pullback (a : H1Etale X (representedSheaf A)) :
    letI := restrictedAction M (inducedGroupHom f s)
    letI := restrictedAction_continuous M (inducedGroupHom f s)
    inverseImageH1AddEquiv f s A hAS hRS M mark hmark hcoeff
      (h1Pullback f (representedSheaf A) a) =
      restriction M (inducedGroupHom f s)
        (representedH1AddEquiv (s ≫ f) A hAX hRX M mark hmark hcoeff a) :=
  representedH1AddEquiv_pullback f s A hAX hAS hRX hRS M mark hmark hcoeff a

/-- The complete actual represented square: scheme pullback followed by an
ordinary coefficient morphism is the single common relative coefficient map. -/
theorem representedH1AddEquiv_pullback_coefficient
    (B : Grp (Over S)) [IsCommMonObj B.X] [IsFinite B.X.hom] [Etale B.X.hom]
    (N : Type v') [AddCommGroup N] [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
    (markB : (Over.mk s ⟶ B.X) ≃* Multiplicative N)
    (hmarkB : ∀ (γ : FiberAutGroup s) b,
      markB (γ.hom.app (coefficientCover B) b) = Multiplicative.ofAdd (γ • (markB b).toAdd))
    (hcoeffB : FiniteCoefficient (representedSheaf B))
    (q : baseChangedGroup f A ⟶ B)
    (ψ : PullbackMap (A := M) (B := N) (inducedGroupHom f s))
    (hq : ∀ a : Over.mk s ⟶ (baseChangedGroup f A).X,
      (markB (a ≫ q.hom.hom)).toAdd = ψ (canonicalPullbackFiberMark f A s mark a).toAdd)
    (a : H1Etale X (representedSheaf A)) :
    representedH1AddEquiv s B hAS hRS N markB hmarkB hcoeffB
      (coefficientMap ((representedSheafBaseChangeIso f A).hom ≫ representedSheafMap q)
        (h1Pullback f (representedSheaf A) a)) =
      ψ.onH1 (representedH1AddEquiv (s ≫ f) A hAX hRX M mark hmark hcoeff a) := by
  let := restrictedAction M (inducedGroupHom f s)
  let := restrictedAction_continuous M (inducedGroupHom f s)
  rw [coefficientMap_comp]
  change representedH1AddEquiv s B hAS hRS N markB hmarkB hcoeffB
    (((coefficientMap (representedSheafMap q)).comp
      (coefficientMap (representedSheafBaseChangeIso f A).hom))
      (h1Pullback f (representedSheaf A) a)) = _
  change representedH1AddEquiv s B hAS hRS N markB hmarkB hcoeffB
    (coefficientMap (representedSheafMap q)
      (coefficientMap (representedSheafBaseChangeIso f A).hom
        (h1Pullback f (representedSheaf A) a))) = _
  rw [representedH1AddEquiv_coefficient s (baseChangedGroup f A) B hAS hRS M N
    (canonicalPullbackFiberMark f A s mark) markB (canonicalPullbackFiberMark_equivariant f A s
      mark hmark)
    hmarkB (pulledBackFiniteCoefficient f A hcoeff) hcoeffB q
    (pullbackCoefficientMap (inducedGroupHom f s) ψ) hq,
    representedH1AddEquiv_pullback f s A hAX hAS hRX hRS M mark hmark hcoeff]
  exact pullbackCoefficientMap_restriction (inducedGroupHom f s) ψ _

end ActualSchemePullback
section SheafCoefficients
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable {L D : AbelianSheaf.{u, u + 1} X}
variable (R : CoefficientRepresentation L) (T : CoefficientRepresentation D)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markL : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M)
variable (markD : (Over.mk s ⟶ T.group.X) ≃* Multiplicative N)
variable (hmarkL : ∀ (γ : FiberAutGroup s) a,
  markL (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (markL a).toAdd))
variable (hmarkD : ∀ (γ : FiberAutGroup s) a,
  markD (γ.hom.app (coefficientCover T.group) a) = Multiplicative.ofAdd (γ • (markD a).toAdd))
variable (hcoeffL : FiniteCoefficient L) (hcoeffD : FiniteCoefficient D)

/-- Naturality for arbitrary finite locally constant abelian coefficient
sheaves and their genuine additive representing isomorphisms. -/
theorem compareH1WithRepresentation_coefficient (q : L ⟶ D)
    (ψ : CoefficientMap (FiberAutGroup s) M N)
    (hq : ∀ a : Over.mk s ⟶ R.group.X,
      (markD (a ≫ (R.map T q).hom.hom)).toAdd = ψ (markL a).toAdd)
    (a : H1Etale X L) :
    compareH1WithRepresentation s hA hR D T N markD hmarkD hcoeffD (coefficientMap q a) =
      ψ.onH1 (compareH1WithRepresentation s hA hR L R M markL hmarkL hcoeffL a) := by
  change representedH1AddEquiv s T.group hA hR N markD hmarkD (hcoeffD.ofIso T.iso)
    (coefficientIso T.iso.symm (coefficientMap q a)) =
    ψ.onH1 (representedH1AddEquiv s R.group hA hR M markL hmarkL (hcoeffL.ofIso R.iso)
      (coefficientIso R.iso.symm a))
  rw [coefficientMap_representation R T q a]
  exact representedH1AddEquiv_coefficient s R.group T.group hA hR M N
    markL markD hmarkL hmarkD (hcoeffL.ofIso R.iso) (hcoeffD.ofIso T.iso)
    (R.map T q) ψ hq _

/-- The preceding square accepts the ordinary compatibility on actual
geometric stalks; the point-marking square is proved from actual sheaf fibres. -/
theorem compareH1WithRepresentation_stalk_coefficient [IsSepClosed K]
    (mL : coefficientFiber s L ≃+ M) (mD : coefficientFiber s D ≃+ N)
    (hmL : ∀ (γ : FiberAutGroup s) a,
      R.pointMark s mL (γ.hom.app (coefficientCover R.group) a) =
        Multiplicative.ofAdd (γ • (R.pointMark s mL a).toAdd))
    (hmD : ∀ (γ : FiberAutGroup s) a,
      T.pointMark s mD (γ.hom.app (coefficientCover T.group) a) =
        Multiplicative.ofAdd (γ • (T.pointMark s mD a).toAdd))
    (q : L ⟶ D) (ψ : CoefficientMap (FiberAutGroup s) M N)
    (hq : ∀ a : coefficientFiber s L,
      mD (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q a) = ψ (mL a))
    (a : H1Etale X L) :
    compareH1WithRepresentation s hA hR D T N (T.pointMark s mD) hmD hcoeffD
      (coefficientMap q a) =
      ψ.onH1 (compareH1WithRepresentation s hA hR L R M (R.pointMark s mL) hmL hcoeffL a) :=
  compareH1WithRepresentation_coefficient s hA hR R T M N _ _ hmL hmD hcoeffL hcoeffD
    q ψ (R.pointMark_naturality s T q mL mD ψ.toAddMonoidHom hq) a

end SheafCoefficients

section SheafPullbackAlgebra
variable {X S : Scheme.{u}} (f : S ⟶ X)
variable {L : AbelianSheaf.{u, u + 1} X} (R : CoefficientRepresentation L)

/-- Pullback of an actual finite coefficient representation uses the actual
base-changed group and the canonical inverse-image represented-sheaf isomorphism. -/
def pulledBackRepresentation : CoefficientRepresentation ((inverseImage f).obj L) where
  group := baseChangedGroup f R.group
  finite := inferInstance
  etale := inferInstance
  commutative := inferInstance
  iso := (representedSheafBaseChangeIso f R.group).symm ≪≫ (inverseImage f).mapIso R.iso

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable {D : AbelianSheaf.{u, u + 1} S} (T : CoefficientRepresentation D)

/-- Reduction of the general sheaf pullback/coefficient map to the actual
base-changed represented group map, before applying any comparison theorem. -/
theorem coefficientMap_pullback_representation (q : (inverseImage f).obj L ⟶ D)
    (a : H1Etale X L) :
    coefficientIso T.iso.symm (coefficientMap q (h1Pullback f L a)) =
      coefficientMap ((representedSheafBaseChangeIso f R.group).hom ≫
        representedSheafMap ((pulledBackRepresentation f R).map T q))
        (h1Pullback f (representedSheaf R.group) (coefficientIso R.iso.symm a)) := by
  rw [coefficientMap_representation (pulledBackRepresentation f R) T q]
  change coefficientMap (representedSheafMap ((pulledBackRepresentation f R).map T q))
    (coefficientMap ((inverseImage f).map R.iso.inv ≫
      (representedSheafBaseChangeIso f R.group).hom) (h1Pullback f L a)) = _
  simp only [coefficientMap_comp, AddMonoidHom.comp_apply, coefficientIso_apply]
  rw [h1Pullback_coefficientMap]
  rfl

end SheafPullbackAlgebra

section ActualStalkPullback
variable {X S : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
variable {L : AbelianSheaf.{u, u + 1} X} (R : CoefficientRepresentation L)

/-- The actual geometric stalk of the inverse-image coefficient is identified
with the original stalk through genuine represented-sheaf stalks and the actual
scheme pullback-fibre equivalence. Every component is an actual additive map. -/
def pullbackStalkEquiv : coefficientFiber s ((inverseImage f).obj L) ≃+
    coefficientFiber (s ≫ f) L :=
  ((pulledBackRepresentation f R).fiberPointEquiv s).trans
    ((Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s R.group).symm.toAdditive.trans
      (R.fiberPointEquiv (s ≫ f)).symm)

/-- The marking obtained from the actual stalk pullback is exactly the canonical
point marking of the actual base-changed coefficient group. -/
theorem pullbackStalkEquiv_pointMark (M : Type v) [AddCommGroup M]
    (mark : coefficientFiber (s ≫ f) L ≃+ M) :
    (pulledBackRepresentation f R).pointMark s ((pullbackStalkEquiv f s R).trans mark) =
      canonicalPullbackFiberMark f R.group s (R.pointMark (s ≫ f) mark) := by
  ext a
  apply Multiplicative.toAdd.injective
  change mark ((R.fiberPointEquiv (s ≫ f)).symm
    ((Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s R.group).symm.toAdditive
      (((pulledBackRepresentation f R).fiberPointEquiv s)
        (((pulledBackRepresentation f R).fiberPointEquiv s).symm (Additive.ofMul a))))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end ActualStalkPullback

section GeneralSchemeCoefficient
variable {X S : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (s ≫ f))]
variable [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [PreconnectedSpace S]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable (hAX : Stacks03AJ.{u, w} X) (hAS : Stacks03AJ.{u, w'} S)
variable (hRX : Stacks03RV X) (hRS : Stacks03RV S)
variable {L : AbelianSheaf.{u, u + 1} X} {D : AbelianSheaf.{u, u + 1} S}
variable (R : CoefficientRepresentation L) (T : CoefficientRepresentation D)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup (s ≫ f)) M] [ContinuousSMul (FiberAutGroup (s ≫ f)) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markL : (Over.mk (s ≫ f) ⟶ R.group.X) ≃* Multiplicative M)
variable (markD : (Over.mk s ⟶ T.group.X) ≃* Multiplicative N)
variable (hmarkL : ∀ (γ : FiberAutGroup (s ≫ f)) a,
  markL (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (markL a).toAdd))
variable (hmarkD : ∀ (γ : FiberAutGroup s) a,
  markD (γ.hom.app (coefficientCover T.group) a) = Multiplicative.ofAdd (γ • (markD a).toAdd))
variable (hcoeffL : FiniteCoefficient L) (hcoeffD : FiniteCoefficient D)

/-- The simultaneous scheme/coefficient naturality theorem for arbitrary
actual finite locally constant abelian sheaves. Its sole marking premise is
an ordinary equation on genuine coefficient points after canonical base change. -/
theorem compareH1WithRepresentation_pullback_coefficient
    (q : (inverseImage f).obj L ⟶ D)
    (ψ : PullbackMap (A := M) (B := N) (inducedGroupHom f s))
    (hq : ∀ a : Over.mk s ⟶ (baseChangedGroup f R.group).X,
      (markD (a ≫ ((pulledBackRepresentation f R).map T q).hom.hom)).toAdd =
        ψ (canonicalPullbackFiberMark f R.group s markL a).toAdd)
    (a : H1Etale X L) :
    compareH1WithRepresentation s hAS hRS D T N markD hmarkD hcoeffD
      (coefficientMap q (h1Pullback f L a)) =
      ψ.onH1 (compareH1WithRepresentation (s ≫ f) hAX hRX L R M markL hmarkL hcoeffL a) := by
  change representedH1AddEquiv s T.group hAS hRS N markD hmarkD (hcoeffD.ofIso T.iso)
    (coefficientIso T.iso.symm (coefficientMap q (h1Pullback f L a))) =
    ψ.onH1 (representedH1AddEquiv (s ≫ f) R.group hAX hRX M markL hmarkL
      (hcoeffL.ofIso R.iso) (coefficientIso R.iso.symm a))
  rw [coefficientMap_pullback_representation f R T q a]
  exact representedH1AddEquiv_pullback_coefficient f s R.group hAX hAS hRX hRS M
    markL hmarkL (hcoeffL.ofIso R.iso) T.group N markD hmarkD (hcoeffD.ofIso T.iso)
    ((pulledBackRepresentation f R).map T q) ψ hq _

/-- The complete simultaneous square expressed on genuine geometric stalks.
The coefficient compatibility is an ordinary equation for the actual stalk map
and the constructed canonical stalk pullback, not an H¹ comparison premise. -/
theorem compareH1WithRepresentation_stalk_pullback_coefficient [IsSepClosed K]
    (mL : coefficientFiber (s ≫ f) L ≃+ M) (mD : coefficientFiber s D ≃+ N)
    (hmL : ∀ (γ : FiberAutGroup (s ≫ f)) b,
      R.pointMark (s ≫ f) mL (γ.hom.app (coefficientCover R.group) b) =
        Multiplicative.ofAdd (γ • (R.pointMark (s ≫ f) mL b).toAdd))
    (hmD : ∀ (γ : FiberAutGroup s) b,
      T.pointMark s mD (γ.hom.app (coefficientCover T.group) b) =
        Multiplicative.ofAdd (γ • (T.pointMark s mD b).toAdd))
    (q : (inverseImage f).obj L ⟶ D)
    (ψ : PullbackMap (A := M) (B := N) (inducedGroupHom f s))
    (hq : ∀ b : coefficientFiber s ((inverseImage f).obj L),
      mD (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q b) =
        ψ (mL (pullbackStalkEquiv f s R b)))
    (a : H1Etale X L) :
    compareH1WithRepresentation s hAS hRS D T N (T.pointMark s mD) hmD hcoeffD
      (coefficientMap q (h1Pullback f L a)) =
      ψ.onH1 (compareH1WithRepresentation (s ≫ f) hAX hRX L R M
        (R.pointMark (s ≫ f) mL) hmL hcoeffL a) := by
  apply compareH1WithRepresentation_pullback_coefficient f s hAX hAS hRX hRS R T M N
    (R.pointMark (s ≫ f) mL) (T.pointMark s mD) hmL hmD hcoeffL hcoeffD q ψ ?_ a
  intro b
  have h := (pulledBackRepresentation f R).pointMark_naturality s T q
    ((pullbackStalkEquiv f s R).trans mL) mD ψ.toAddMonoidHom hq b
  rw [pullbackStalkEquiv_pointMark] at h
  exact h

end GeneralSchemeCoefficient

section RepresentationIndependence
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} X) (R T : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : coefficientFiber s L ≃+ M)
variable (hRmark : ∀ (γ : FiberAutGroup s) a,
  R.pointMark s mark (γ.hom.app (coefficientCover R.group) a) =
    Multiplicative.ofAdd (γ • (R.pointMark s mark a).toAdd))
variable (hTmark : ∀ (γ : FiberAutGroup s) a,
  T.pointMark s mark (γ.hom.app (coefficientCover T.group) a) =
    Multiplicative.ofAdd (γ • (T.pointMark s mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- The actual-stalk-marked additive comparison is independent of the finite
coefficient representation. This is deduced from actual coefficient naturality
for the identity of L, rather than supplied as a classification premise. -/
theorem compareH1WithRepresentation_independent (a : H1Etale X L) :
    compareH1WithRepresentation s hA hR L T M (T.pointMark s mark) hTmark hcoeff a =
      compareH1WithRepresentation s hA hR L R M (R.pointMark s mark) hRmark hcoeff a := by
  have h := compareH1WithRepresentation_stalk_coefficient s hA hR R T M M
    hcoeff hcoeff mark mark hRmark hTmark (𝟙 L) CoefficientMap.id
    (by
      intro x
      change mark (((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map (𝟙 L) x) = mark x
      exact congrArg mark (ConcreteCategory.congr_hom
        (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map_id L) x)) a
  simpa only [coefficientMap_id, AddMonoidHom.id_apply, CoefficientMap.onH1_id] using h

end RepresentationIndependence

section PointedBaseChange
variable {X S : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
variable (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x)

/-- The actual pointed scheme map, with its point-preserving equality retained
explicitly rather than silently identifying fibre automorphism groups. -/
def pointedGroupHom : FiberAutGroup s →ₜ* FiberAutGroup x :=
  { pointedMap (Under.homMk f hx : Under.mk s ⟶ Under.mk x) with
    continuous_toFun := continuous_pointedMap _ }

/-- For a composite target point this is exactly the existing actual induced map. -/
@[simp] theorem pointedGroupHom_rfl :
    pointedGroupHom f s (s ≫ f) rfl = inducedGroupHom f s := rfl

/-- The continuous pointed projection has exactly the frozen projectionHom
underlying group homomorphism, including its non-definitional point transport. -/
theorem pointedGroupHom_projection {B : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    (pointedGroupHom p (b ≫ o) b (by simp [Category.assoc, h])).toMonoidHom =
      projectionHom b p o h := rfl

/-- The actual pointed section is exactly the frozen origin homomorphism. -/
theorem pointedGroupHom_origin {B : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (o : B ⟶ X) :
    (pointedGroupHom o b (b ≫ o) rfl).toMonoidHom = originHom b o := rfl

variable (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
variable (M : Type v) [AddCommGroup M]
variable (mark : (Over.mk x ⟶ A.X) ≃* Multiplicative M)

/-- The canonical actual coefficient-fibre marking for a point-preserving map.
Equality elimination exposes precisely the canonical pullback-fibre marking. -/
def pointedPullbackFiberMark : (Over.mk s ⟶ (baseChangedGroup f A).X) ≃* Multiplicative M := by
  subst x
  exact canonicalPullbackFiberMark f A s mark

variable [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup x) M] [ContinuousSMul (FiberAutGroup x) M]
variable (hmark : ∀ (γ : FiberAutGroup x) a,
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

include hmark in
/-- The canonical pointed marking has the restricted actual monodromy action. -/
theorem pointedPullbackFiberMark_equivariant :
    letI := restrictedAction M (pointedGroupHom f s x hx)
    ∀ (γ : FiberAutGroup s) a,
      pointedPullbackFiberMark f s x hx A M mark (γ.hom.app (coefficientCover (baseChangedGroup f
        A)) a) =
        Multiplicative.ofAdd (γ • (pointedPullbackFiberMark f s x hx A M mark a).toAdd) := by
  subst x
  exact canonicalPullbackFiberMark_equivariant f A s mark hmark

variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
variable [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [PreconnectedSpace S]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable [Finite M]
variable (hAX : Stacks03AJ.{u, w} X) (hAS : Stacks03AJ.{u, w'} S)
variable (hRX : Stacks03RV X) (hRS : Stacks03RV S)
variable (hcoeff : FiniteCoefficient (representedSheaf A))

/-- The actual inverse-image coefficient-sheaf comparison for a pointed map,
with its group action restricted along the literal pointed homomorphism. -/
def pointedInverseImageH1AddEquiv :
    letI := restrictedAction M (pointedGroupHom f s x hx)
    letI := restrictedAction_continuous M (pointedGroupHom f s x hx)
    H1Etale S ((inverseImage f).obj (representedSheaf A)) ≃+ H1 (FiberAutGroup s) M := by
  letI := restrictedAction M (pointedGroupHom f s x hx)
  letI := restrictedAction_continuous M (pointedGroupHom f s x hx)
  exact (coefficientIso (representedSheafBaseChangeIso f A)).trans
    (representedH1AddEquiv s (baseChangedGroup f A) hAS hRS M
      (pointedPullbackFiberMark f s x hx A M mark)
      (pointedPullbackFiberMark_equivariant f s x hx A M mark hmark)
      (pulledBackFiniteCoefficient f A hcoeff))

/-- Naturality for actual pointed scheme maps. This includes rational projections
whose composite point equals the chosen field point only propositionally. -/
theorem representedH1AddEquiv_pointed_pullback (a : H1Etale X (representedSheaf A)) :
    letI := restrictedAction M (pointedGroupHom f s x hx)
    letI := restrictedAction_continuous M (pointedGroupHom f s x hx)
    representedH1AddEquiv s (baseChangedGroup f A) hAS hRS M
      (pointedPullbackFiberMark f s x hx A M mark)
      (pointedPullbackFiberMark_equivariant f s x hx A M mark hmark)
      (pulledBackFiniteCoefficient f A hcoeff)
      (coefficientMap (representedSheafBaseChangeIso f A).hom (h1Pullback f (representedSheaf A)
        a)) =
      restriction M (pointedGroupHom f s x hx)
        (representedH1AddEquiv x A hAX hRX M mark hmark hcoeff a) := by
  subst x
  exact representedH1AddEquiv_pullback f s A hAX hAS hRX hRS M mark hmark hcoeff a

/-- The pointed literal-inverse-image comparison satisfies the actual pointed
scheme square, with the complete basepoint transport visible in its type. -/
theorem pointedInverseImageH1AddEquiv_pullback (a : H1Etale X (representedSheaf A)) :
    letI := restrictedAction M (pointedGroupHom f s x hx)
    letI := restrictedAction_continuous M (pointedGroupHom f s x hx)
    pointedInverseImageH1AddEquiv f s x hx A M mark hmark hAS hRS hcoeff
      (h1Pullback f (representedSheaf A) a) =
      restriction M (pointedGroupHom f s x hx)
        (representedH1AddEquiv x A hAX hRX M mark hmark hcoeff a) :=
  representedH1AddEquiv_pointed_pullback f s x hx A M mark hmark hAX hAS hRX hRS hcoeff a

end PointedBaseChange

section GeneralMarking
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} X) (R : CoefficientRepresentation L)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (markM : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M)
variable (markN : (Over.mk s ⟶ R.group.X) ≃* Multiplicative N)
variable (hmarkM : ∀ (γ : FiberAutGroup s) b,
  markM (γ.hom.app (coefficientCover R.group) b) = Multiplicative.ofAdd (γ • (markM b).toAdd))
variable (hmarkN : ∀ (γ : FiberAutGroup s) b,
  markN (γ.hom.app (coefficientCover R.group) b) = Multiplicative.ofAdd (γ • (markN b).toAdd))
variable (e : M ≃+ N) (he : ∀ (γ : FiberAutGroup s) b, e (γ • b) = γ • e b)
variable (hm : ∀ b : Over.mk s ⟶ R.group.X, (markN b).toAdd = e (markM b).toAdd)
variable (hcoeff : FiniteCoefficient L)

include hm in
/-- The arbitrary-sheaf comparison commutes with genuine coefficient markings
and universe changes, with the induced map on the existing common quotient. -/
theorem compareH1WithRepresentation_marking (a : H1Etale X L) :
    compareH1WithRepresentation s hA hR L R N markN hmarkN hcoeff a =
      coefficientH1Equiv e he
        (compareH1WithRepresentation s hA hR L R M markM hmarkM hcoeff a) :=
  MarkedComparisonTransport.representedH1AddEquiv_marking s R.group M N markM markN
    hmarkM hmarkN e he hm hA hR (hcoeff.ofIso R.iso) (coefficientIso R.iso.symm a)

end GeneralMarking

section IntrinsicCanonicalNaturality
open MarkedComparisonTransport
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (L D : AbelianSheaf.{u, u + 1} X)
variable (hL : FiniteCoefficient L) (hD : FiniteCoefficient D)
variable (M : Type v) (N : Type v') [AddCommGroup M] [AddCommGroup N] [Finite M] [Finite N]
variable [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable [DistribMulAction (FiberAutGroup s) N] [ContinuousSMul (FiberAutGroup s) N]
variable (mL : coefficientFiber s L ≃+ M) (mD : coefficientFiber s D ≃+ N)
variable (hmL : ∀ (γ : FiberAutGroup s) b,
  mL (stalkEvaluation s (finiteCoefficientRepresentation hR L hL) γ b) = γ • mL b)
variable (hmD : ∀ (γ : FiberAutGroup s) b,
  mD (stalkEvaluation s (finiteCoefficientRepresentation hR D hD) γ b) = γ • mD b)

/-- Coefficient naturality for the canonical arbitrary-sheaf comparison whose
marking is equivariant for the intrinsic actual stalk action. -/
theorem compareH1OfStalkMark_coefficient (q : L ⟶ D)
    (ψ : CoefficientMap (FiberAutGroup s) M N)
    (hq : ∀ b : coefficientFiber s L,
      mD (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q b) = ψ (mL b))
    (a : H1Etale X L) :
    compareH1OfStalkMark s hA hR D hD N mD hmD (coefficientMap q a) =
      ψ.onH1 (compareH1OfStalkMark s hA hR L hL M mL hmL a) :=
  compareH1WithRepresentation_stalk_coefficient s hA hR
    (finiteCoefficientRepresentation hR L hL) (finiteCoefficientRepresentation hR D hD) M N
    hL hD mL mD (pointMark_equivariant_of_stalk s _ mL hmL)
    (pointMark_equivariant_of_stalk s _ mD hmD) q ψ hq a

include hmL in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Intrinsic equivariance is retained under any other genuine finite coefficient
representation, because the actual stalk action was proved representation-independent. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem intrinsicMark_equivariant (R : CoefficientRepresentation L)
    (γ : FiberAutGroup s) (b : coefficientFiber s L) :
    mL (stalkEvaluation s R γ b) = γ • mL b := by
  rw [stalkEvaluation_independent s R (finiteCoefficientRepresentation hR L hL)]
  exact hmL γ b

/-- The canonical comparison can be calculated using any actual coefficient
representation. Its equality with that calculation is proved, not an input. -/
theorem compareH1OfStalkMark_withRepresentation (R : CoefficientRepresentation L)
    (a : H1Etale X L) :
    compareH1OfStalkMark s hA hR L hL M mL hmL a =
      compareH1WithRepresentation s hA hR L R M (R.pointMark s mL)
        (pointMark_equivariant_of_stalk s R mL (intrinsicMark_equivariant s hR L hL M mL hmL R))
          hL a :=
  compareH1WithRepresentation_independent s hA hR L R
    (finiteCoefficientRepresentation hR L hL) M mL
    (pointMark_equivariant_of_stalk s R mL (intrinsicMark_equivariant s hR L hL M mL hmL R))
    (pointMark_equivariant_of_stalk s _ mL hmL) hL a

end IntrinsicCanonicalNaturality

end AlgebraicGeometry.Scheme.EtaleCohomology.Naturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 33fffed6abf7312e95681aeeab5b37ac693a77091c0c7785286b1fff86293fae.
Definitions, hypotheses and universes are retained modulo native names. -/
