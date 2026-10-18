/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FundamentalGroupComparison
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.SchemeTorsorBaseChange

/-!
# Marking and universe transport for the actual fundamental-group comparison

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Marking changes act by literal
postcomposition on positive transport cocycles in the existing common H¹.
Scheme pullback uses the actual point-fibre equivalence and uniqueness of
scheme-point transport. No lifted action equality or comparison square is assumed.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality
namespace AlgebraicGeometry.Scheme.EtaleH1.MarkedComparisonTransport
open FundamentalGroupComparison MarkedCoefficients SchemeTorsorClassification
open GroupCohomology.ContinuousH1
universe u v v' w w'
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian hasSheafifyLarge

section IntrinsicMonodromy
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]

/-- Actual natural evaluation preserves the coefficient identity, by naturality
of its unit morphism from the genuine terminal finite-etale cover. -/
theorem evaluation_one (γ : FiberAutGroup s) :
    γ.hom.app (coefficientCover H) (1 : Over.mk s ⟶ H.X) = (1 : Over.mk s ⟶ H.X) := by
  have h := Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ
    (Z := 𝟙_ (Scheme.FiniteEtale X))
    (W := coefficientCover H) (η[H.X]) (toUnit (Over.mk s))
  change γ.hom.app (coefficientCover H) (1 : Over.mk s ⟶ H.X) =
    γ.hom.app (𝟙_ (Scheme.FiniteEtale X)) (toUnit (Over.mk s)) ≫ η[H.X] at h
  calc
    _ = γ.hom.app (𝟙_ (Scheme.FiniteEtale X)) (toUnit (Over.mk s)) ≫ η[H.X] := h
    _ = toUnit (Over.mk s) ≫ η[H.X] := congrArg (fun p => p ≫ η[H.X])
      (toUnit_unique (γ.hom.app (𝟙_ (Scheme.FiniteEtale X)) (toUnit (Over.mk s)))
        (toUnit (Over.mk s)))
    _ = 1 := rfl

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Actual evaluation preserves coefficient multiplication, by naturality of
the group law on the universal finite-etale product. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem evaluation_mul (γ : FiberAutGroup s) (a b : Over.mk s ⟶ H.X) :
    γ.hom.app (coefficientCover H) (a * b) =
      (show Over.mk s ⟶ H.X from γ.hom.app (coefficientCover H) a) *
        (show Over.mk s ⟶ H.X from γ.hom.app (coefficientCover H) b) := by
  have h := Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ
    (Z := coefficientCover H ⊗ coefficientCover H)
    (W := coefficientCover H) (μ[H.X]) (lift a b)
  rw [evaluation_product s H (coefficientCover H)] at h
  exact h

/-- Intrinsic monodromy on actual coefficient points. No marked module or
external action is used: scalar action is the actual natural fibre evaluation. -/
@[instance_reducible] def pointEvaluationAction :
    DistribMulAction (FiberAutGroup s) (PointModule s H) where
  smul γ a := Additive.ofMul (γ.hom.app (coefficientCover H) a.toMul)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero γ := congrArg Additive.ofMul (evaluation_one s H γ)
  smul_add γ a b := congrArg Additive.ofMul (evaluation_mul s H γ a.toMul b.toMul)

/-- The intrinsic finite coefficient action is continuous for the actual
fibre-automorphism evaluation topology and the discrete point topology. -/
theorem pointEvaluationContinuousSMul :
    letI := pointEvaluationAction s H
    ContinuousSMul (FiberAutGroup s) (PointModule s H) := by
  let := pointEvaluationAction s H
  exact PreGaloisCategory.continuousSMul_aut_fiber (fiberToFinite s) (coefficientCover H)

variable [IsSepClosed K]
variable {L : AbelianSheaf.{u, u + 1} X} (R : CoefficientRepresentation L)

/-- Intrinsic monodromy of the actual stalk, explicitly induced by natural
evaluation on its proved representing finite coefficient group. -/
def stalkEvaluation (γ : FiberAutGroup s) (a : coefficientFiber s L) : coefficientFiber s L :=
  (R.fiberPointEquiv s).symm (Additive.ofMul
    (γ.hom.app (coefficientCover R.group) (R.fiberPointEquiv s a).toMul))

/-- The stalk action evaluates to the literal actual coefficient-point action. -/
theorem stalkEvaluation_points (γ : FiberAutGroup s) (a : coefficientFiber s L) :
    R.fiberPointEquiv s (stalkEvaluation s R γ a) =
      Additive.ofMul (γ.hom.app (coefficientCover R.group) (R.fiberPointEquiv s a).toMul) :=
  (R.fiberPointEquiv s).apply_symm_apply _

/-- The intrinsic stalk action is a distributive group action, constructed
without any given external coefficient action or fibre marking. -/
@[instance_reducible] def stalkEvaluationAction :
    DistribMulAction (FiberAutGroup s) (coefficientFiber s L) := by
  letI := pointEvaluationAction s R.group
  let e := R.fiberPointEquiv s
  exact { e.toEquiv.mulAction (FiberAutGroup s) with
    smul_zero γ := by change e.symm (γ • e 0) = 0; simp
    smul_add γ a b := by
      change e.symm (γ • e (a + b)) = e.symm (γ • e a) + e.symm (γ • e b)
      simp [smul_add] }

/-- Scalar multiplication in the constructed action is the explicit intrinsic map. -/
theorem stalkEvaluationAction_smul (γ : FiberAutGroup s) (a : coefficientFiber s L) :
    letI := stalkEvaluationAction s R
    γ • a = stalkEvaluation s R γ a := rfl

/-- Finite geometric stalks have their discrete topology. -/
@[instance_reducible] def coefficientFiberTopology : TopologicalSpace (coefficientFiber s L) := ⊥

/-- Joint continuity of intrinsic stalk monodromy, independently of a marking. -/
theorem stalkEvaluationContinuousSMul :
    letI := coefficientFiberTopology s (L := L)
    letI := stalkEvaluationAction s R
    ContinuousSMul (FiberAutGroup s) (coefficientFiber s L) := by
  let := coefficientFiberTopology s (L := L)
  let : DiscreteTopology (coefficientFiber s L) := ⟨rfl⟩
  let := pointEvaluationAction s R.group
  let := pointEvaluationContinuousSMul s R.group
  let := stalkEvaluationAction s R
  let e := R.fiberPointEquiv s
  exact ⟨(continuous_of_discreteTopology (f := e.symm)).comp
    (continuous_fst.smul ((continuous_of_discreteTopology (f := e)).comp continuous_snd))⟩

/-- Every ordinary coefficient sheaf map is equivariant for the intrinsic
stalk actions, by genuine representing-map and fibre-evaluation naturality. -/
theorem stalkEvaluation_naturality {N : AbelianSheaf.{u, u + 1} X}
    (S : CoefficientRepresentation N) (q : L ⟶ N)
    (γ : FiberAutGroup s) (a : coefficientFiber s L) :
    stalkEvaluation s S γ (((Scheme.pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).map q a) =
      ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q
        (stalkEvaluation s R γ a) := by
  apply (S.fiberPointEquiv s).injective
  rw [stalkEvaluation_points, R.fiberPointEquiv_naturality s S q,
    R.fiberPointEquiv_naturality s S q, stalkEvaluation_points]
  exact congrArg Additive.ofMul
    (Scheme.FiniteEtale.FiberTorsorActions.evaluation_naturality s γ
          (Z := coefficientCover R.group) (W := coefficientCover S.group)
      (R.map S q).hom.hom (R.fiberPointEquiv s a).toMul)

/-- The intrinsic stalk evaluation is independent of the finite coefficient
representative, derived using the actual morphism representing the identity sheaf map. -/
theorem stalkEvaluation_independent (S : CoefficientRepresentation L)
    (γ : FiberAutGroup s) (a : coefficientFiber s L) :
    stalkEvaluation s R γ a = stalkEvaluation s S γ a := by
  have h := stalkEvaluation_naturality s R S (𝟙 L) γ a
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hi (b : coefficientFiber s L) : F.map (𝟙 L) b = b :=
    ConcreteCategory.congr_hom (F.map_id L) b
  exact (hi _).symm.trans (h.symm.trans (congrArg (stalkEvaluation s S γ) (hi a)))

/-- The constructed distributive stalk action itself is representation-independent. -/
theorem stalkEvaluationAction_independent (S : CoefficientRepresentation L) :
    stalkEvaluationAction s R = stalkEvaluationAction s S := by
  ext γ a
  exact stalkEvaluation_independent s R S γ a

/-- Ordinary equivariance of an actual stalk marking for intrinsic monodromy
implies exactly the point-marking condition used by the canonical comparison. -/
theorem pointMark_equivariant_of_stalk {M : Type v} [AddCommGroup M]
    [DistribMulAction (FiberAutGroup s) M] (mark : coefficientFiber s L ≃+ M)
    (hmark : ∀ (γ : FiberAutGroup s) a, mark (stalkEvaluation s R γ a) = γ • mark a)
    (γ : FiberAutGroup s) (a : Over.mk s ⟶ R.group.X) :
    R.pointMark s mark (γ.hom.app (coefficientCover R.group) a) =
      Multiplicative.ofAdd (γ • (R.pointMark s mark a).toAdd) := by
  apply Multiplicative.toAdd.injective
  rw [R.pointMark_apply, R.pointMark_apply]
  have h := hmark γ ((R.fiberPointEquiv s).symm (Additive.ofMul a))
  unfold stalkEvaluation at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h

end IntrinsicMonodromy

section Marking
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
variable (M₀ : Type v) (M : Type v') [AddCommGroup M₀] [AddCommGroup M]
variable [Finite M₀] [Finite M] [TopologicalSpace M₀] [TopologicalSpace M]
variable [DiscreteTopology M₀] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M₀] [ContinuousSMul (FiberAutGroup s) M₀]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark₀ : (Over.mk s ⟶ H.X) ≃* Multiplicative M₀)
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark₀ : ∀ (γ : FiberAutGroup s) a,
  mark₀ (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark₀ a).toAdd))
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (e : M₀ ≃+ M) (he : ∀ (γ : FiberAutGroup s) a, e (γ • a) = γ • e a)
variable (hm : ∀ a : Over.mk s ⟶ H.X, (mark a).toAdd = e (mark₀ a).toAdd)

include hm in
/-- Changing the actual marking postcomposes the actual positive transport cocycle. -/
theorem markedBasedCocycle_marking (Y : Scheme.FiniteEtale X) (τ : TorsorAction H (toUnit Y.obj))
    (t : Fiber s Y) :
    markedBasedCocycle s H M mark hmark Y τ t =
      (coefficientMapOfEquiv e he).onCocycles (markedBasedCocycle s H M₀ mark₀ hmark₀ Y τ t) := by
  apply Cocycle.ext
  intro γ
  rw [CoefficientMap.onCocycles_apply, markedBasedCocycle_apply, markedBasedCocycle_apply]
  exact hm _

include hm in
/-- The additive comparison respects actual equivariant marking equivalences
across arbitrary coefficient universes. The proof evaluates genuine torsors. -/
theorem representedH1AddEquiv_marking (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (hcoeff : FiniteCoefficient (representedSheaf H)) (a : H1Etale X (representedSheaf H)) :
    representedH1AddEquiv s H hA hR M mark hmark hcoeff a =
      coefficientH1Equiv e he (representedH1AddEquiv s H hA hR M₀ mark₀ hmark₀ hcoeff a) := by
  obtain ⟨p, rfl⟩ := (hA.bijective (representedSheaf H)).surjective a
  refine Quotient.inductionOn p ?_
  intro P
  let Y := P.finiteEtaleRepresentative hR hcoeff.locally_constant
  let d := P.finiteEtaleRepresentativeIso hR hcoeff.locally_constant
  let : Surjective Y.obj.hom := P.represented_surjective H Y d
  let : Nonempty (Fiber s Y) := nonempty_fiber_of_surjective s Y
  let t : Fiber s Y := Classical.choice inferInstance
  change representedH1AddEquiv _ _ _ _ _ _ _ _ (torsorExtClass P) =
    coefficientH1Equiv e he (representedH1AddEquiv _ _ _ _ _ _ _ _ (torsorExtClass P))
  rw [representedH1AddEquiv_torsor_representative s H hA hR M mark hmark hcoeff P Y d t,
    representedH1AddEquiv_torsor_representative s H hA hR M₀ mark₀ hmark₀ hcoeff P Y d t,
    coefficientH1Equiv_classOf,
    markedBasedCocycle_marking s H M₀ M mark₀ mark hmark₀ hmark e he hm]

/-- On a genuine scheme torsor the comparison uses its original action exactly,
by the proved represented-action roundtrip. This holds in every marking universe. -/
theorem representedH1AddEquiv_schemeAction
    (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
    (hcoeff : FiniteCoefficient (representedSheaf H)) (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] (τ : TorsorAction H (toUnit Y.obj)) (t : Fiber s Y) :
    representedH1AddEquiv s H hA hR M mark hmark hcoeff
      (torsorExtClass (torsorOfSchemeAction H Y τ)) =
      classOf (FiberAutGroup s) M (markedBasedCocycle s H M mark hmark Y τ t) := by
  have h := representedH1AddEquiv_torsor_representative s H hA hR M mark hmark hcoeff
    (torsorOfSchemeAction H Y τ) Y (Iso.refl _) t
  rw [torsorOfSchemeAction_representedSchemeAction] at h
  exact h

include hmark in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The small point action previously transported through an external marking
is equal to intrinsic evaluation, using the proved point-marking equation. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pointModuleAction_eq_evaluation :
    pointModuleAction s H M mark = pointEvaluationAction s H := by
  ext γ a
  exact pointModuleAction_evaluation s H M mark hmark γ a.toMul

end Marking

section Pullback
variable {X S : Scheme.{u}} (f : S ⟶ X)
variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
variable (M : Type v) [AddCommGroup M]
variable (mark : (Over.mk (s ≫ f) ⟶ H.X) ≃* Multiplicative M)

/-- The canonical pulled-back coefficient marking, without a universe restriction. -/
def pullbackFiberMark : (Over.mk s ⟶ (baseChangedGroup f H).X) ≃* Multiplicative M :=
  (pullbackFiberMulEquiv f s H).symm.trans mark

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Positive transport commutes with actual scheme pullback by its unique action equation. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem transport_pullback (Y : Scheme.FiniteEtale X) (τ : TorsorAction H (toUnit Y.obj))
    (t x : Fiber (s ≫ f) Y) :
    transport s (baseChangedGroup f H) ((baseChange f).obj Y)
      (SchemeTorsorBaseChange.pullbackSchemeAction f H Y τ)
      (fiberBaseChangeEquiv f s Y t) (fiberBaseChangeEquiv f s Y x) =
      pullbackFiberMulEquiv f s H (transport (s ≫ f) H Y τ t x) := by
  apply (transport_unique s (baseChangedGroup f H) ((baseChange f).obj Y)
    (SchemeTorsorBaseChange.pullbackSchemeAction f H Y τ) _ _ _ ?_).symm
  rw [SchemeTorsorBaseChange.pullbackSchemeAction_fiber, transport_act]

variable [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (s ≫ f)) M] [ContinuousSMul (FiberAutGroup (s ≫ f)) M]
variable (hmark : ∀ (γ : FiberAutGroup (s ≫ f)) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

include hmark in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The arbitrary-universe pullback marking is equivariant for the actual
induced fundamental-group map and its restricted linear action. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pullbackFiberMark_equivariant :
    letI := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
    ∀ (γ : FiberAutGroup s) a,
      pullbackFiberMark f s H M mark (γ.hom.app (coefficientCover (baseChangedGroup f H)) a) =
        Multiplicative.ofAdd (γ • (pullbackFiberMark f s H M mark a).toAdd) := by
  let := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
  intro γ a
  change mark ((fiberBaseChangeEquiv f s (coefficientCover H)).symm
      (γ.hom.app ((baseChange f).obj (coefficientCover H)) a)) =
    Multiplicative.ofAdd ((inducedGroupHom f s γ) •
      (mark ((fiberBaseChangeEquiv f s (coefficientCover H)).symm a)).toAdd)
  rw [fiberBaseChange_equivariant]
  exact hmark _ _

variable [Finite M]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (s ≫ f))]
variable [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [PreconnectedSpace S]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The actual arbitrary-universe marked cocycle of the pulled-back scheme
torsor is literal restriction, with positive transport preserved. -/
theorem markedBasedCocycle_pullback (Y : Scheme.FiniteEtale X) (τ : TorsorAction H (toUnit Y.obj))
    (t : Fiber (s ≫ f) Y) :
    letI := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
    letI := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
    markedBasedCocycle s (baseChangedGroup f H) M (pullbackFiberMark f s H M mark)
      (pullbackFiberMark_equivariant f s H M mark hmark) ((baseChange f).obj Y)
      (SchemeTorsorBaseChange.pullbackSchemeAction f H Y τ) (fiberBaseChangeEquiv f s Y t) =
    restrictionCocycles M (inducedGroupHom f s) (markedBasedCocycle (s ≫ f) H M mark hmark Y τ t)
      := by
  let := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
  let := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
  apply Cocycle.ext
  intro γ
  rw [restrictionCocycles_apply, markedBasedCocycle_apply, markedBasedCocycle_apply]
  have he : γ.hom.app ((baseChange f).obj Y) (fiberBaseChangeEquiv f s Y t) =
      fiberBaseChangeEquiv f s Y ((inducedGroupHom f s γ).hom.app Y t) := by
    apply (fiberBaseChangeEquiv f s Y).symm.injective
    rw [Equiv.symm_apply_apply, fiberBaseChange_equivariant, Equiv.symm_apply_apply]
  rw [he, transport_pullback]
  exact congrArg Multiplicative.toAdd (mark.congr_arg ((pullbackFiberMulEquiv f s
    H).symm_apply_apply _))

end Pullback

section IntrinsicComparison
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} X) (hcoeff : FiniteCoefficient L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : coefficientFiber s L ≃+ M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (stalkEvaluation s (finiteCoefficientRepresentation hR L hcoeff) γ a) = γ • mark a)

/-- The canonical finite-coefficient comparison expressed solely with a marking
of the genuine stalk equivariant for its intrinsic actual monodromy action. -/
def compareH1OfStalkMark : H1Etale X L ≃+ H1 (FiberAutGroup s) M :=
  compareH1 s hA hR L hcoeff M mark
    (pointMark_equivariant_of_stalk s (finiteCoefficientRepresentation hR L hcoeff) mark hmark)

/-- Intrinsic-stalk formulation retains the exact original positive-transport
representative, rather than an unspecified additive comparison. -/
theorem compareH1OfStalkMark_torsor_representative (P : Torsor L) (Y : Scheme.FiniteEtale X)
    (d : finiteRepresentedSetSheaf Y ≅ P.carrier) (t : Fiber s Y) :
    compareH1OfStalkMark s hA hR L hcoeff M mark hmark (torsorExtClass P) =
      classOf (FiberAutGroup s) M
        (markedBasedCocycle s (finiteCoefficientRepresentation hR L hcoeff).group M
          ((finiteCoefficientRepresentation hR L hcoeff).pointMark s mark)
          (pointMark_equivariant_of_stalk s (finiteCoefficientRepresentation hR L hcoeff) mark
            hmark)
          Y ((P.ofCoefficientIso (finiteCoefficientRepresentation hR L
            hcoeff).iso.symm).representedSchemeAction (finiteCoefficientRepresentation hR L
            hcoeff).group Y d) t) :=
  compareH1_torsor_representative s hA hR L hcoeff M mark
    (pointMark_equivariant_of_stalk s (finiteCoefficientRepresentation hR L hcoeff) mark hmark) P
      Y d t

end IntrinsicComparison

end AlgebraicGeometry.Scheme.EtaleH1.MarkedComparisonTransport

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 104cf8c294869c5baf90d7b30e6c9a8b01c43984379df84ace66eb83f5755368.
Definitions, hypotheses and universes are retained modulo native names. -/
