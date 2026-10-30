/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Naturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientStalkBaseChange
public import Aglib.GroupCohomology.H1.SplitCoordinates
public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricKernel

/-!
# Actual projection, section and geometric restriction in étale H¹

Generic A5 constructions for `K2-018#eq:k2018-pointed-character`, frozen
engineering basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
The coefficients are actual inverse-image sheaves. The continuous group maps
are the existing actual pointed projection, origin and geometric inclusion.
The section coefficient map is the inverse-image composition/identity transport.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
open Naturality FundamentalGroupComparison
open GroupCohomology.ContinuousH1
universe u v w w'
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

section SplitScheme
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)

include h in
/-- The canonical point-preserving equality of the split projection. -/
theorem projection_point : (b ≫ o) ≫ p = b := by simp [Category.assoc, h]

/-- The actual continuous projection, including the canonical transport from
its composite geometric point to the displayed base point. -/
def projection : FiberAutGroup (b ≫ o) →ₜ* FiberAutGroup b :=
  pointedGroupHom p (b ≫ o) b (projection_point b p o h)

/-- The actual continuous section induced by the given scheme section. -/
def sectionHom : FiberAutGroup b →ₜ* FiberAutGroup (b ≫ o) :=
  pointedGroupHom o b (b ≫ o) rfl

/-- The projected group section is literally the frozen projectionHom. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF]
theorem projection_toMonoidHom : (projection b p o h).toMonoidHom = projectionHom b p o h
  := rfl

/-- The group section is literally the frozen originHom. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF]
theorem sectionHom_toMonoidHom : (sectionHom b o).toMonoidHom = originHom b o := rfl

/-- The actual scheme section gives an actual continuous group retraction. -/
@[simp] theorem projection_section (γ : FiberAutGroup b) :
    projection b p o h (sectionHom b o γ) = γ := originHom_projectionHom_apply b p o h γ

end SplitScheme

section BaseComparison
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable (hAB : Stacks03AJ.{u, w} B) (hAX : Stacks03AJ.{u, w'} X)
variable (hRB : Stacks03RV B) (hRX : Stacks03RV X)
variable (A : Grp (Over B)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable (mark : (Over.mk b ⟶ A.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup b) a,
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf A))

/-- The comparison for the actual pulled-back coefficient sheaf on X, with
its action literally inflated through the actual pointed projection. -/
def baseH1AddEquiv :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    H1Etale X ((inverseImage p).obj (representedSheaf A)) ≃+ H1 (FiberAutGroup (b ≫ o)) M :=
  pointedInverseImageH1AddEquiv p (b ≫ o) b (projection_point b p o h)
    A M mark hmark hAX hRX hcoeff

/-- Base inflation is restriction along the frozen actual projectionHom,
with the non-definitional composite-basepoint transport explicitly constructed. -/
theorem base_inflation (a : H1Etale B (representedSheaf A)) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    baseH1AddEquiv b p o h hAX hRX A M mark hmark hcoeff (h1Pullback p (representedSheaf A) a) =
      restriction M (projection b p o h)
        (representedH1AddEquiv b A hAB hRB M mark hmark hcoeff a) :=
  pointedInverseImageH1AddEquiv_pullback p (b ≫ o) b (projection_point b p o h)
    A M mark hmark hAB hAX hRB hRX hcoeff a

end BaseComparison

section StalkMarkings
open CoefficientStalkBaseChange
variable {B X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]

/-- An actual coefficient-point marking induces the corresponding marking on
the genuine geometric stalk through the proved additive representing isomorphism. -/
def representationStalkMark (b : Spec (CommRingCat.of K) ⟶ B)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    (M : Type v) [AddCommGroup M] (mark : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M) :
    coefficientFiber b L ≃+ M := (R.fiberPointEquiv b).trans mark.toAdditiveLeft

/-- Returning to actual coefficient points preserves the original marking exactly. -/
theorem representationStalkMark_pointMark (b : Spec (CommRingCat.of K) ⟶ B)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    (M : Type v) [AddCommGroup M] (mark : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M) :
    R.pointMark b (representationStalkMark b R M mark) = mark := by
  ext a
  apply Multiplicative.toAdd.injective
  change mark.toAdditiveLeft ((R.fiberPointEquiv b) ((R.fiberPointEquiv b).symm (Additive.ofMul
    a))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The genuine pointed stalk transport has precisely the canonical pointed
coefficient marking used in actual scheme naturality. -/
theorem pointedStalkMark_pointMark (f : X ⟶ B)
    (s : Spec (CommRingCat.of K) ⟶ X) (b : Spec (CommRingCat.of K) ⟶ B) (hb : s ≫ f = b)
    {L : AbelianSheaf.{u, u + 1} B} (R : CoefficientRepresentation L)
    (M : Type v) [AddCommGroup M] (mark : coefficientFiber b L ≃+ M) :
    (pulledBackRepresentation f R).pointMark s
      ((pointedPullbackStalkEquiv f s L b hb R).trans mark) =
      pointedPullbackFiberMark f s b hb R.group M (R.pointMark b mark) := by
  subst b
  exact pullbackStalkEquiv_pointMark f s R M mark

end StalkMarkings

section CanonicalSectionStalk

variable {B X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
  (L : AbelianSheaf.{u, u + 1} B)

/-- The original section coefficient is the composite of the two actual canonical inverses. -/
theorem canonical_section_stalk_pullback
    (a : coefficientFiber b ((inverseImage o).obj ((inverseImage p).obj L))) :
    ((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        (sectionCoefficientIso p o h L).hom a =
      pointedCanonicalPullbackStalkEquiv p (b ≫ o) L b (projection_point b p o h)
        (pointedCanonicalPullbackStalkEquiv o b ((inverseImage p).obj L) (b ≫ o) rfl a) := by
  let Ep := pointedCanonicalPullbackStalkEquiv p (b ≫ o) L b (projection_point b p o h)
  let Eo := pointedCanonicalPullbackStalkEquiv o b ((inverseImage p).obj L) (b ≫ o) rfl
  let c := ((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
    (sectionCoefficientIso p o h L).hom
  have hc (x : coefficientFiber b L) : c (Eo.symm (Ep.symm x)) = x := by
    have hs := ConcreteCategory.congr_hom
      (CoefficientStalkBaseChange.section_stalkUnit b p o h L) x
    change c (CoefficientStalkBaseChange.pointedStalkUnit o b ((inverseImage p).obj L)
      (b ≫ o) rfl (CoefficientStalkBaseChange.pointedStalkUnit p (b ≫ o) L b
        (projection_point b p o h) x)) = x at hs
    rw [pointedStalkUnit_eq_canonical_inverse, pointedStalkUnit_eq_canonical_inverse] at hs
    exact hs
  exact GrothendieckTopology.Point.UnitTransport.inverse_section
    Ep.symm.toEquiv Eo.symm.toEquiv c hc a

end CanonicalSectionStalk

section GeneralBaseComparison
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite b)]
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [PreconnectedSpace B] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} B)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
variable (hAB : Stacks03AJ.{u, w} B) (hAX : Stacks03AJ.{u, w'} X)
variable (hRB : Stacks03RV B) (hRX : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} B) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup b) M] [ContinuousSMul (FiberAutGroup b) M]
variable (mark : (Over.mk b ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup b) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- The actual pulled-back arbitrary coefficient comparison, using a proved
additive finite representation only to calculate the canonical comparison. -/
def generalBaseH1AddEquiv :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    H1Etale X ((inverseImage p).obj L) ≃+ H1 (FiberAutGroup (b ≫ o)) M := by
  letI := restrictedAction M (projection b p o h)
  letI := restrictedAction_continuous M (projection b p o h)
  exact (coefficientIso ((inverseImage p).mapIso R.iso.symm)).trans
    (baseH1AddEquiv b p o h hAX hRX R.group M mark hmark (hcoeff.ofIso R.iso))

/-- Base inflation for every finite locally constant abelian coefficient sheaf,
with the actual geometric point transport and actual projection still explicit. -/
theorem general_base_inflation (a : H1Etale B L) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff (h1Pullback p L a) =
      restriction M (projection b p o h)
        (compareH1WithRepresentation b hAB hRB L R M mark hmark hcoeff a) := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  change baseH1AddEquiv b p o h hAX hRX R.group M mark hmark (hcoeff.ofIso R.iso)
    (coefficientMap ((inverseImage p).map R.iso.inv) (h1Pullback p L a)) = _
  rw [← h1Pullback_coefficientMap p R.iso.inv a]
  exact base_inflation b p o h hAB hAX hRB hRX R.group M mark hmark
    (hcoeff.ofIso R.iso) (coefficientIso R.iso.symm a)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The pulled-back comparison is exactly calculation through the actual
base-changed coefficient representation, with its canonical pointed marking. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem generalBaseH1AddEquiv_representation (a : H1Etale X ((inverseImage p).obj L)) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a =
      compareH1WithRepresentation (b ≫ o) hAX hRX ((inverseImage p).obj L)
        (pulledBackRepresentation p R) M
        (pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) R.group M mark)
        (pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h)
          R.group M mark hmark) (hcoeff.pullback p) a := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let m := pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) R.group M mark
  have hm := pointedPullbackFiberMark_equivariant p (b ≫ o) b
    (projection_point b p o h) R.group M mark hmark
  let hc := pulledBackFiniteCoefficient p R.group (hcoeff.ofIso R.iso)
  change representedH1AddEquiv (b ≫ o) (baseChangedGroup p R.group) hAX hRX M m hm hc
    (coefficientMap (representedSheafBaseChangeIso p R.group).hom
      (coefficientMap ((inverseImage p).map R.iso.inv) a)) =
    representedH1AddEquiv (b ≫ o) (baseChangedGroup p R.group) hAX hRX M m hm hc
      (coefficientMap (((inverseImage p).map R.iso.inv) ≫
        (representedSheafBaseChangeIso p R.group).hom) a)
  simp only [coefficientMap_comp, AddMonoidHom.comp_apply]

/-- Actual origin pullback is restriction along the actual section. The
coefficient identity is proved on genuine stalks from the adjunction-unit
Comp/Id coherence; no marking or cohomology comparison square is assumed. -/
theorem general_origin_square [IsSepClosed K]
    (a : H1Etale.{u, u + 1, w'} X ((inverseImage p).obj L)) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction_continuous M (projection b p o h)
    compareH1WithRepresentation b hAB hRB L R M mark hmark hcoeff
      (sectionPullback p o h L a) =
      GroupCohomology.SplitCoordinates.sectionRestriction (A := M) (projection b p o h)
        (sectionHom b o)
        (projection_section b p o h)
        (generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a) := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction_continuous M (projection b p o h)
  let RX := pulledBackRepresentation p R
  let mB := representationStalkMark b R M mark
  let mX := (pointedCanonicalPullbackStalkEquiv p (b ≫ o) L b
    (projection_point b p o h)).trans mB
  have hb : R.pointMark b mB = mark := representationStalkMark_pointMark b R M mark
  have hx : RX.pointMark (b ≫ o) mX =
      pointedPullbackFiberMark p (b ≫ o) b (projection_point b p o h) R.group M mark := by
    change (pulledBackRepresentation p R).pointMark (b ≫ o)
      ((CoefficientStalkBaseChange.pointedPullbackStalkEquiv p (b ≫ o) L b
        (projection_point b p o h) R).trans mB) = _
    rw [pointedStalkMark_pointMark, hb]
  have hmB : ∀ (γ : FiberAutGroup b) t,
      R.pointMark b mB (γ.hom.app (coefficientCover R.group) t) =
        Multiplicative.ofAdd (γ • (R.pointMark b mB t).toAdd) := by
    rw [hb]
    exact hmark
  have hmX : ∀ (γ : FiberAutGroup (b ≫ o)) t,
      RX.pointMark (b ≫ o) mX (γ.hom.app (coefficientCover RX.group) t) =
        Multiplicative.ofAdd (γ • (RX.pointMark (b ≫ o) mX t).toAdd) := by
    rw [hx]
    exact pointedPullbackFiberMark_equivariant p (b ≫ o) b (projection_point b p o h)
      R.group M mark hmark
  let ψ := GroupCohomology.SplitCoordinates.sectionPullbackMap (A := M) (projection b p o h)
    (sectionHom b o)
    (projection_section b p o h)
  have hq : ∀ t : coefficientFiber b ((inverseImage o).obj ((inverseImage p).obj L)),
      mB (((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        (sectionCoefficientIso p o h L).hom t) = ψ (mX (pullbackStalkEquiv o b RX t)) := by
    intro t
    change mB (((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((inverseImageComp p o).inv.app L ≫
        eqToHom (congrArg (fun k : B ⟶ B => (inverseImage k).obj L) h) ≫
        (inverseImageId B).hom.app L) t) = _
    exact congrArg mB (canonical_section_stalk_pullback b p o h L t)
  have hn := compareH1WithRepresentation_stalk_pullback_coefficient o b hAX hAB hRX hRB
    RX R M M (hcoeff.pullback p) hcoeff mX mB hmX hmB
    (sectionCoefficientIso p o h L).hom ψ hq a
  simp only [hb, hx] at hn
  change compareH1WithRepresentation b hAB hRB L R M mark hmark hcoeff
    (coefficientMap (sectionCoefficientIso p o h L).hom
      (h1Pullback o ((inverseImage p).obj L) a)) =
      ψ.onH1 (generalBaseH1AddEquiv b p o h hAX hRX L R M mark hmark hcoeff a)
  rw [generalBaseH1AddEquiv_representation b p o h hAX hRX L R M mark hmark hcoeff a]
  exact hn

end GeneralBaseComparison

section TrivialKernelAction
variable {E G A : Type*} [Group E] [Group G]
variable [TopologicalSpace E] [TopologicalSpace G]
variable [AddCommGroup A] [DistribMulAction G A]
variable (p : E →ₜ* G)

/-- Coefficients inflated through an actual projection are trivial on its actual kernel. -/
theorem inflatedAction_kernel (n : p.toMonoidHom.ker) (a : A) :
    letI := restrictedAction A p
    (n : E) • a = a := by
  let := restrictedAction A p
  change p.toMonoidHom n • a = a
  rw [n.property, one_smul]

end TrivialKernelAction

section TrivialGeometricAction
open AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable (M : Type v) [AddCommGroup M] [DistribMulAction (FiberAutGroup b) M]

/-- The actual geometric inclusion as a continuous group homomorphism. -/
def geometricInclusion : BaseChangeGroup b p o h →ₜ* FiberAutGroup (b ≫ o) :=
  { baseChangeHom b p o h with continuous_toFun := continuous_baseChangeHom b p o h }

/-- Actual pullback from the base has trivial geometric monodromy, proved from
the actual pointed pullback square and the identity-point automorphism group. -/
theorem geometric_action_trivial (γ : BaseChangeGroup b p o h) (a : M) :
    letI := restrictedAction M (projection b p o h)
    letI := restrictedAction M (geometricInclusion b p o h)
    γ • a = a := by
  let := restrictedAction M (projection b p o h)
  let := restrictedAction M (geometricInclusion b p o h)
  change projectionHom b p o h (baseChangeHom b p o h γ) • a = a
  rw [projection_baseChangeHom, one_smul]

end TrivialGeometricAction
section GeometricComparison
open AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [GaloisCategory (Scheme.FiniteEtale (pullback p b))]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite (baseChangePoint b p o h))]
variable [PreconnectedSpace X] [PreconnectedSpace (pullback p b : Scheme.{u})]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p b))]
variable (hAX : Stacks03AJ.{u, w} X) (hAG : Stacks03AJ.{u, w'} (pullback p b))
variable (hRX : Stacks03RV X) (hRG : Stacks03RV (pullback p b))
variable (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (b ≫ o)) M] [ContinuousSMul (FiberAutGroup (b ≫ o)) M]
variable (mark : (Over.mk (b ≫ o) ⟶ A.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup (b ≫ o)) a,
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf A))

/-- The actual geometric inverse-image comparison, with literal coefficient
sheaf pullback and the existing geometric pointed group homomorphism. -/
def geometricH1AddEquiv :
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    H1Etale (pullback p b) ((inverseImage (pullback.fst p b)).obj (representedSheaf A)) ≃+
      H1 (BaseChangeGroup b p o h) M :=
  pointedInverseImageH1AddEquiv (pullback.fst p b) (baseChangePoint b p o h) (b ≫ o)
    (baseChangePoint_fst b p o h) A M mark hmark hAG hRG hcoeff

/-- Geometric restriction uses the actual geometricHom (baseChangeHom for a
general base point), without identifying it definitionally with the projection kernel. -/
theorem geometric_restriction (a : H1Etale X (representedSheaf A)) :
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    geometricH1AddEquiv b p o h hAG hRG A M mark hmark hcoeff
      (h1Pullback (pullback.fst p b) (representedSheaf A) a) =
      restriction M (geometricInclusion b p o h)
        (representedH1AddEquiv (b ≫ o) A hAX hRX M mark hmark hcoeff a) :=
  pointedInverseImageH1AddEquiv_pullback (pullback.fst p b) (baseChangePoint b p o h) (b ≫ o)
    (baseChangePoint_fst b p o h) A M mark hmark hAX hAG hRX hRG hcoeff a

/-- The geometric square on an actual continuous-cocycle representative is
literal precomposition with the existing geometric inclusion. -/
theorem geometric_restriction_classOf (c : Cocycle (FiberAutGroup (b ≫ o)) M) :
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    geometricH1AddEquiv b p o h hAG hRG A M mark hmark hcoeff
      (h1Pullback (pullback.fst p b) (representedSheaf A)
        ((representedH1AddEquiv (b ≫ o) A hAX hRX M mark hmark hcoeff).symm
          (classOf (FiberAutGroup (b ≫ o)) M c))) =
      classOf (BaseChangeGroup b p o h) M (restrictionCocycles M (geometricInclusion b p o h) c)
        := by
  let := restrictedAction M (geometricInclusion b p o h)
  let := restrictedAction_continuous M (geometricInclusion b p o h)
  rw [geometric_restriction b p o h hAX hAG hRX hRG A M mark hmark hcoeff,
    AddEquiv.apply_symm_apply, restriction_classOf]

end GeometricComparison

section GeneralGeometricComparison
open AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
variable {B X : Scheme.{u}} {K : Type u} [Field K]
variable (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
variable (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
  (fiberToFinite (b ≫ o))]
variable [GaloisCategory (Scheme.FiniteEtale (pullback p b))]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite (baseChangePoint b p o h))]
variable [PreconnectedSpace X] [PreconnectedSpace (pullback p b : Scheme.{u})]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p b))]
variable (hAX : Stacks03AJ.{u, w} X) (hAG : Stacks03AJ.{u, w'} (pullback p b))
variable (hRX : Stacks03RV X) (hRG : Stacks03RV (pullback p b))
variable (L : AbelianSheaf.{u, u + 1} X) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (b ≫ o)) M] [ContinuousSMul (FiberAutGroup (b ≫ o)) M]
variable (mark : (Over.mk (b ≫ o) ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup (b ≫ o)) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- The genuine geometric inverse-image comparison for an arbitrary finite
locally constant abelian coefficient sheaf, calculated through a proved representation. -/
def generalGeometricH1AddEquiv :
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    H1Etale (pullback p b) ((inverseImage (pullback.fst p b)).obj L) ≃+
      H1 (BaseChangeGroup b p o h) M := by
  letI := restrictedAction M (geometricInclusion b p o h)
  letI := restrictedAction_continuous M (geometricInclusion b p o h)
  exact (coefficientIso ((inverseImage (pullback.fst p b)).mapIso R.iso.symm)).trans
    (geometricH1AddEquiv b p o h hAG hRG R.group M mark hmark (hcoeff.ofIso R.iso))

/-- Geometric restriction for actual arbitrary coefficient sheaves uses the
actual pointed geometric homomorphism, with no kernel identification assumed. -/
theorem general_geometric_restriction (a : H1Etale X L) :
    letI := restrictedAction M (geometricInclusion b p o h)
    letI := restrictedAction_continuous M (geometricInclusion b p o h)
    generalGeometricH1AddEquiv b p o h hAG hRG L R M mark hmark hcoeff
      (h1Pullback (pullback.fst p b) L a) =
      restriction M (geometricInclusion b p o h)
        (compareH1WithRepresentation (b ≫ o) hAX hRX L R M mark hmark hcoeff a) := by
  let := restrictedAction M (geometricInclusion b p o h)
  let := restrictedAction_continuous M (geometricInclusion b p o h)
  change geometricH1AddEquiv b p o h hAG hRG R.group M mark hmark (hcoeff.ofIso R.iso)
    (coefficientMap ((inverseImage (pullback.fst p b)).map R.iso.inv)
      (h1Pullback (pullback.fst p b) L a)) = _
  rw [← h1Pullback_coefficientMap (pullback.fst p b) R.iso.inv a]
  exact geometric_restriction b p o h hAX hAG hRX hRG R.group M mark hmark
    (hcoeff.ofIso R.iso) (coefficientIso R.iso.symm a)

end GeneralGeometricComparison

section ConditionalGeometricKernel
open AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
variable (F : Type u) [Field F] (h0BTX : Stacks0BTX F)
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of F))
variable (o : Spec (CommRingCat.of F) ⟶ X) (h : o ≫ p = 𝟙 _)
variable [IsProper p] [GeometricallyConnected p]
variable (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
variable [DistribMulAction (FiberAutGroup (algebraicClosurePoint F ≫ o)) M]
variable [ContinuousSMul (FiberAutGroup (algebraicClosurePoint F ≫ o)) M]

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The conditional geometric/kernel identification preserves literal cocycle
evaluation. No arbitrary equivalence with the projection kernel is substituted. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem geometric_kernel_cocycle
    (c : Cocycle (FiberAutGroup (algebraicClosurePoint F ≫ o)) M)
    (γ : GeometricGroup F p o h) :
    c.val (geometricHom F p o h γ) =
      c.val (geometricKernelContinuousEquiv F h0BTX p o h γ :
        FiberAutGroup (algebraicClosurePoint F ≫ o)) := rfl

end ConditionalGeometricKernel

end AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d37622d9eb89f978fd7f6f0d0ff927901f0e5e0a6d4b4b4983b2f99294ce8885.
Definitions, hypotheses and universes are retained modulo native names. -/
