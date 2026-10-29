/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorComparisonAdditivity
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedComparisonNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.CategoryTheory.Sites.Torsor.CoefficientIso

/-!
# The actual finite-coefficient fundamental-group comparison

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The additive comparison uses
canonical extension classes, actual coefficient-sheaf isomorphisms and the
proved contracted-sum comparison. Its representative formulas retain literal
positive transport and the given geometric fibre marking, including across
coefficient universes.
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
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u v w
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian hasSheafifyLarge

/-- Actual coefficient isomorphisms preserve the displayed positive annihilator
and its invertibility, as well as the geometric local trivializations. -/
def FiniteCoefficient.ofIso {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (h : FiniteCoefficient L) (e : N ≅ L) : FiniteCoefficient N where
  level := h.level
  positive := h.positive
  invertible := h.invertible
  locally_constant := (isFiniteLocallyConstant_iff_of_iso e).mpr h.locally_constant
  killed := by
    change h.level • (𝟙 N) = 0
    have hh := congrArg (fun f : L ⟶ L => e.hom ≫ f ≫ e.inv) h.killed
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      e.hom_inv_id, comp_zero, zero_comp] using hh

/-- Transport of a genuine torsor through an actual coefficient isomorphism:
the sheaf of sections is unchanged and the action uses the inverse coefficient map. -/
abbrev Torsor.ofCoefficientIso {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (P : Torsor L) (e : L ≅ N) : Torsor N :=
  CategoryTheory.Sheaf.Torsor.ofCoefficientIso P e

/-- The identity on the carrier is genuinely equivariant for the coefficient iso. -/
abbrev Torsor.coefficientIsoHom {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (P : Torsor L) (e : L ≅ N) : Torsor.Hom e.hom P (P.ofCoefficientIso e) :=
  CategoryTheory.Sheaf.Torsor.coefficientIsoHom P e

/-- The reverse identity carrier map has the inverse actual coefficient. -/
abbrev Torsor.coefficientIsoInvHom {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (P : Torsor L) (e : L ≅ N) : Torsor.Hom e.inv (P.ofCoefficientIso e) P :=
  CategoryTheory.Sheaf.Torsor.coefficientIsoInvHom P e

/-- Canonical extension classes commute with this literal coefficient transport. -/
theorem torsorExtClass_ofCoefficientIso {X : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] {L N : AbelianSheaf.{u, u + 1} X}
    (P : Torsor L) (e : L ≅ N) :
    coefficientIso e (torsorExtClass P) = torsorExtClass (P.ofCoefficientIso e) :=
  CategoryTheory.Sheaf.torsorExtClass_ofCoefficientIso P e

/-- An ordinary sheaf coefficient morphism gives its actual finite group-scheme
morphism by the proved represented-coefficient full faithfulness. -/
def CoefficientRepresentation.map {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N) (q : L ⟶ N) :
    R.group ⟶ S.group := representedSheafGroupPreimage (R.iso.hom ≫ q ≫ S.iso.inv)

/-- The recovered group-scheme morphism represents the original sheaf map exactly. -/
theorem CoefficientRepresentation.map_sheaf {X : Scheme.{u}} {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N) (q : L ⟶ N) :
    representedSheafMap (R.map S q) = R.iso.hom ≫ q ≫ S.iso.inv :=
  representedSheafMap_preimage _

/-- The ordinary coefficient square commutes before any cohomology comparison. -/
@[reassoc] theorem CoefficientRepresentation.map_square {X : Scheme.{u}}
    {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N) (q : L ⟶ N) :
    R.iso.inv ≫ representedSheafMap (R.map S q) = q ≫ S.iso.inv := by
  rw [R.map_sheaf S q, R.iso.inv_hom_id_assoc]

/-- Actual Ext coefficient transport reduces any sheaf coefficient map to its
proved finite represented group-scheme map. This is a derived functor square. -/
theorem coefficientMap_representation {X : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N)
    (q : L ⟶ N) (a : H1Etale X L) :
    coefficientIso S.iso.symm (coefficientMap q a) =
      coefficientMap (representedSheafMap (R.map S q)) (coefficientIso R.iso.symm a) := by
  change coefficientMap S.iso.inv (coefficientMap q a) =
    coefficientMap (representedSheafMap (R.map S q)) (coefficientMap R.iso.inv a)
  change ((coefficientMap S.iso.inv).comp (coefficientMap q)) a =
    ((coefficientMap (representedSheafMap (R.map S q))).comp (coefficientMap R.iso.inv)) a
  rw [← coefficientMap_comp, ← coefficientMap_comp, R.map_square S q]

section StalkMarking
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ X)

/-- The genuine small-etale geometric fibre, formed by the actual point's sheaf fibre functor. -/
abbrev coefficientFiber (L : AbelianSheaf.{u, u + 1} X) :=
  ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj L

/-- A genuine additive representing isomorphism identifies the actual stalk
with actual coefficient scheme points. The intermediate ULift is explicitly removed. -/
def CoefficientRepresentation.fiberPointEquiv {L : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) :
    coefficientFiber s L ≃+ MarkedCoefficients.PointModule s R.group :=
  (Iso.addCommGroupIsoToAddEquiv
    (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso R.iso.symm)).trans
    ((Iso.addCommGroupIsoToAddEquiv (representedFiberIso s R.group)).trans AddEquiv.ulift)

/-- The fibre equivalence is exactly evaluation after the actual stalk map
of the inverse representing sheaf isomorphism. -/
theorem CoefficientRepresentation.fiberPointEquiv_apply {L : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (a : coefficientFiber s L) :
    R.fiberPointEquiv s a =
      (representedFiberEvaluation s R.group
        (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map R.iso.inv
          a)).down := rfl

/-- A marking of the actual stalk gives the group-point marking used by descent. -/
def CoefficientRepresentation.pointMark {L : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) {M : Type v} [AddCommGroup M]
    (mark : coefficientFiber s L ≃+ M) : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M :=
  ((R.fiberPointEquiv s).symm.trans mark).toMultiplicativeRight

/-- The point marking applies the original stalk marking to its genuine germ. -/
theorem CoefficientRepresentation.pointMark_apply {L : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) {M : Type v} [AddCommGroup M]
    (mark : coefficientFiber s L ≃+ M) (a : Over.mk s ⟶ R.group.X) :
    (R.pointMark s mark a).toAdd = mark ((R.fiberPointEquiv s).symm (Additive.ofMul a)) := rfl

/-- Finiteness of a locally constant coefficient's genuine geometric stalk
follows from the proved finite scheme-point identification. -/
theorem CoefficientRepresentation.fiber_finite {L : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) : Finite (coefficientFiber s L) :=
  Finite.of_equiv (MarkedCoefficients.PointModule s R.group) (R.fiberPointEquiv s).symm.toEquiv

/-- The actual stalk-point comparison commutes with every ordinary coefficient
sheaf map, using the group-scheme morphism recovered by full faithfulness. -/
theorem CoefficientRepresentation.fiberPointEquiv_naturality
    {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N)
    (q : L ⟶ N) (a : coefficientFiber s L) :
    S.fiberPointEquiv s
        (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q a) =
      Additive.ofMul ((R.fiberPointEquiv s a).toMul ≫ (R.map S q).hom.hom) := by
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have h : F.map S.iso.inv (F.map q a) =
      F.map (representedSheafMap (R.map S q)) (F.map R.iso.inv a) := by
    have hh := congrArg (fun f : L ⟶ representedSheaf S.group => F.map f a) (R.map_square S q)
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh.symm
  rw [S.fiberPointEquiv_apply, h, representedFiberEvaluation_naturality]
  rfl

/-- Ordinary compatibility on genuine geometric stalks implies the exact
point-marking square needed for the represented coefficient comparison. -/
theorem CoefficientRepresentation.pointMark_naturality
    {L N : AbelianSheaf.{u, u + 1} X}
    (R : CoefficientRepresentation L) (S : CoefficientRepresentation N)
    (q : L ⟶ N) {M : Type v} {D : Type*} [AddCommGroup M] [AddCommGroup D]
    (markL : coefficientFiber s L ≃+ M) (markN : coefficientFiber s N ≃+ D)
    (φ : M →+ D)
    (hq : ∀ a : coefficientFiber s L,
      markN (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map q a) = φ
        (markL a))
    (a : Over.mk s ⟶ R.group.X) :
    (S.pointMark s markN (a ≫ (R.map S q).hom.hom)).toAdd =
      φ (R.pointMark s markL a).toAdd := by
  rw [S.pointMark_apply, R.pointMark_apply]
  have h := R.fiberPointEquiv_naturality s S q ((R.fiberPointEquiv s).symm (Additive.ofMul a))
  rw [AddEquiv.apply_symm_apply] at h
  have hh := congrArg (S.fiberPointEquiv s).symm h
  rw [AddEquiv.symm_apply_apply] at hh
  exact (congrArg markN hh).symm.trans (hq _)

end StalkMarking

namespace FundamentalGroupComparison
open MarkedCoefficients SchemeTorsorClassification TorsorComparisonAdditivity ContinuousTorsors
open GroupCohomology.ContinuousH1
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)

section SmallComparison
variable (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf H))

/-- The small marked coefficient comparison uses the actual descended sheaf iso. -/
def smallRepresentedH1AddEquiv : H1Etale X (representedSheaf H) ≃+ H1 (FiberAutGroup s) M :=
  (coefficientIso (moduleSheafIso s H M mark hmark).symm).trans
    (moduleH1AddEquiv s M hA hR (hcoeff.ofIso (moduleSheafIso s H M mark hmark)))

/-- The small comparison evaluates on every genuine torsor by its original
represented scheme action and its original marking. -/
theorem smallRepresentedH1AddEquiv_torsor (P : Torsor (representedSheaf H)) :
    smallRepresentedH1AddEquiv s H hA hR M mark hmark hcoeff (torsorExtClass P) =
      representedTorsorClass s H mark hmark hR hcoeff.locally_constant P := by
  let e := moduleSheafIso s H M mark hmark
  let Q := P.ofCoefficientIso e.symm
  change moduleH1AddEquiv s M hA hR (hcoeff.ofIso e)
    (coefficientIso e.symm (torsorExtClass P)) = _
  rw [torsorExtClass_ofCoefficientIso, moduleH1AddEquiv_torsor]
  have hn := representedTorsorClass_naturality (moduleScheme s M) H
    (moduleGroupIso s H M mark hmark).hom (P.coefficientIsoInvHom e.symm)
    s (moduleFiberMulEquiv s M) mark (moduleFiber_action s M) hmark
    (coefficientMapOfEquiv (AddEquiv.refl M) (fun _ _ => rfl))
    (fun a => congrArg Multiplicative.toAdd (moduleGroupIso_marking s H M mark hmark a))
    hR (moduleSheaf_isFiniteLocallyConstant (s := s) M) hcoeff.locally_constant
  exact hn.symm

end SmallComparison

section UniverseComparison
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf H))

omit [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [IsFinite H.X.hom] [Etale H.X.hom] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (FiberAutGroup s) M] in
/-- The actual point-module marking intertwines the specified linear actions. -/
theorem pointModuleEquiv_equivariant :
    letI := pointModuleAction s H M mark
    ∀ (γ : FiberAutGroup s) a,
      pointModuleEquiv s H M mark (γ • a) = γ • pointModuleEquiv s H M mark a := by
  let := pointModuleAction s H M mark
  intro γ a
  exact (pointModuleEquiv s H M mark).apply_symm_apply _

/-- Actual Ext H¹ is additively equivalent to the one common continuous H¹,
for a finite represented coefficient with an arbitrary-universe geometric marking. -/
def representedH1AddEquiv : H1Etale X (representedSheaf H) ≃+ H1 (FiberAutGroup s) M := by
  letI := pointModuleAction s H M mark
  letI := pointModuleContinuousSMul s H M mark
  exact (smallRepresentedH1AddEquiv s H hA hR (PointModule s H) (pointModuleMark s H)
    (pointModuleMark_equivariant s H M mark hmark) hcoeff).trans
    (coefficientH1Equiv (pointModuleEquiv s H M mark)
      (pointModuleEquiv_equivariant s H M mark))

/-- Representative evaluation before the explicit coefficient-universe map. -/
theorem representedH1AddEquiv_torsor_pointModule (P : Torsor (representedSheaf H)) :
    letI := pointModuleAction s H M mark
    letI := pointModuleContinuousSMul s H M mark
    representedH1AddEquiv s H hA hR M mark hmark hcoeff (torsorExtClass P) =
      coefficientH1Equiv (pointModuleEquiv s H M mark)
        (pointModuleEquiv_equivariant s H M mark)
        (representedTorsorClass s H (pointModuleMark s H)
          (pointModuleMark_equivariant s H M mark hmark) hR hcoeff.locally_constant P) := by
  let := pointModuleAction s H M mark
  let := pointModuleContinuousSMul s H M mark
  change coefficientH1Equiv _ _
    (smallRepresentedH1AddEquiv s H hA hR (PointModule s H) (pointModuleMark s H)
      (pointModuleMark_equivariant s H M mark hmark) hcoeff (torsorExtClass P)) = _
  rw [smallRepresentedH1AddEquiv_torsor]

/-- The arbitrary-universe cocycle is the common small-point cocycle followed
by the given marking; no new cocycle quotient or action is introduced. -/
def markedBasedCocycle (Y : Scheme.FiniteEtale X)
    (τ : CategoryTheory.TorsorAction H (toUnit Y.obj))
    (t : Fiber s Y) : Cocycle (FiberAutGroup s) M := by
  letI := pointModuleAction s H M mark
  letI := pointModuleContinuousSMul s H M mark
  exact (coefficientMapOfEquiv (pointModuleEquiv s H M mark)
    (pointModuleEquiv_equivariant s H M mark)).onCocycles
    (basedCocycle s H Y τ (pointModuleMark s H)
      (pointModuleMark_equivariant s H M mark hmark) t)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Its value is exactly the original mark of positive actual transport. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem markedBasedCocycle_apply (Y : Scheme.FiniteEtale X)
    (τ : CategoryTheory.TorsorAction H (toUnit Y.obj))
    (t : Fiber s Y) (γ : FiberAutGroup s) :
    (markedBasedCocycle s H M mark hmark Y τ t).val γ =
      (mark (transport s H Y τ t (γ.hom.app Y t))).toAdd := by
  let := pointModuleAction s H M mark
  let := pointModuleContinuousSMul s H M mark
  change (pointModuleEquiv s H M mark)
    ((basedCocycle s H Y τ (pointModuleMark s H)
      (pointModuleMark_equivariant s H M mark hmark) t).val γ) = _
  rw [basedCocycle_apply]
  rfl

/-- The actual point-action equation fixes the positive displacement convention
also when the marked coefficient lives in another universe. -/
theorem markedBasedCocycle_action (Y : Scheme.FiniteEtale X)
    (τ : CategoryTheory.TorsorAction H (toUnit Y.obj))
    (t : Fiber s Y) (γ : FiberAutGroup s) :
    τ.act (mark.symm (Multiplicative.ofAdd
      ((markedBasedCocycle s H M mark hmark Y τ t).val γ))) t = γ.hom.app Y t := by
  rw [markedBasedCocycle_apply]
  change τ.act (mark.symm (mark _)) t = _
  rw [mark.symm_apply_apply]
  exact transport_act s H Y τ t _

/-- Any actual finite étale representative and any actual fibre point compute
the arbitrary-universe comparison by the displayed positive marked cocycle. -/
theorem representedH1AddEquiv_torsor_representative (P : Torsor (representedSheaf H))
    (Y : Scheme.FiniteEtale X) (e : finiteRepresentedSetSheaf Y ≅ P.carrier) (t : Fiber s Y) :
    representedH1AddEquiv s H hA hR M mark hmark hcoeff (torsorExtClass P) =
      classOf (FiberAutGroup s) M
        (markedBasedCocycle s H M mark hmark Y (P.representedSchemeAction H Y e) t) := by
  let := pointModuleAction s H M mark
  let := pointModuleContinuousSMul s H M mark
  let : Nonempty (Fiber s Y) := ⟨t⟩
  rw [representedH1AddEquiv_torsor_pointModule,
    representedTorsorClass_eq s H (pointModuleMark s H)
      (pointModuleMark_equivariant s H M mark hmark) hR hcoeff.locally_constant P Y e,
    schemeTorsorClass_eq s H Y (P.representedSchemeAction H Y e)
      (pointModuleMark s H) (pointModuleMark_equivariant s H M mark hmark) t]
  rfl

end UniverseComparison

section DirectRepresentativeFormula
variable (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient (representedSheaf H))

/-- In the small coefficient universe the public comparison is literally the
previously constructed represented-torsor class for the original marking. -/
theorem representedH1AddEquiv_torsor (P : Torsor (representedSheaf H)) :
    representedH1AddEquiv s H hA hR M mark hmark hcoeff (torsorExtClass P) =
      representedTorsorClass s H mark hmark hR hcoeff.locally_constant P := by
  let := pointModuleAction s H M mark
  let := pointModuleContinuousSMul s H M mark
  rw [representedH1AddEquiv_torsor_pointModule]
  let r : Torsor.Hom (representedSheafMap (𝟙 H)) P P :=
    { map := 𝟙 P.carrier
      equivariant := by intro U a t; rw [representedSheafMap_id]; rfl }
  exact (representedTorsorClass_naturality H H (𝟙 H) r s
    (pointModuleMark s H) mark (pointModuleMark_equivariant s H M mark hmark) hmark
    (coefficientMapOfEquiv (pointModuleEquiv s H M mark)
      (pointModuleEquiv_equivariant s H M mark))
    (by intro a; change (mark (a ≫ 𝟙 H.X)).toAdd = (mark a).toAdd; rw [Category.comp_id])
    hR hcoeff.locally_constant hcoeff.locally_constant).symm

end DirectRepresentativeFormula
section GeneralCoefficient
variable (L : AbelianSheaf.{u, u + 1} X) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

/-- The arbitrary finite coefficient comparison for any actual additive
representing isomorphism. The representation supplies no cohomology map. -/
def compareH1WithRepresentation : H1Etale X L ≃+ H1 (FiberAutGroup s) M :=
  (coefficientIso R.iso.symm).trans
    (representedH1AddEquiv s R.group hA hR M mark hmark (hcoeff.ofIso R.iso))

/-- The general comparison is definitionally the actual coefficient-iso
transport followed by the proved represented comparison. -/
theorem compareH1WithRepresentation_apply (a : H1Etale X L) :
    compareH1WithRepresentation s hA hR L R M mark hmark hcoeff a =
      representedH1AddEquiv s R.group hA hR M mark hmark (hcoeff.ofIso R.iso)
        (coefficientIso R.iso.symm a) := rfl

/-- Every actual torsor computes the general comparison after literal
coefficient transport through the given additive representing isomorphism. -/
theorem compareH1WithRepresentation_torsor_representative (P : Torsor L)
    (Y : Scheme.FiniteEtale X) (e : finiteRepresentedSetSheaf Y ≅ P.carrier) (t : Fiber s Y) :
    compareH1WithRepresentation s hA hR L R M mark hmark hcoeff (torsorExtClass P) =
      classOf (FiberAutGroup s) M (markedBasedCocycle s R.group M mark hmark Y
        ((P.ofCoefficientIso R.iso.symm).representedSchemeAction R.group Y e) t) := by
  change representedH1AddEquiv s R.group hA hR M mark hmark (hcoeff.ofIso R.iso)
    (coefficientIso R.iso.symm (torsorExtClass P)) = _
  rw [torsorExtClass_ofCoefficientIso]
  exact representedH1AddEquiv_torsor_representative s R.group hA hR M mark hmark
    (hcoeff.ofIso R.iso) (P.ofCoefficientIso R.iso.symm) Y e t

end GeneralCoefficient

/-- In the small marking universe the general coefficient comparison has the
same literal selected-representative formula used for coefficient naturality. -/
theorem compareH1WithRepresentation_torsor
    (L : AbelianSheaf.{u, u + 1} X) (R : CoefficientRepresentation L)
    (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
    (mark : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup s) a,
      mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
    (hcoeff : FiniteCoefficient L) (P : Torsor L) :
    compareH1WithRepresentation s hA hR L R M mark hmark hcoeff (torsorExtClass P) =
      representedTorsorClass s R.group mark hmark hR (hcoeff.ofIso R.iso).locally_constant
        (P.ofCoefficientIso R.iso.symm) := by
  change representedH1AddEquiv s R.group hA hR M mark hmark (hcoeff.ofIso R.iso)
    (coefficientIso R.iso.symm (torsorExtClass P)) = _
  rw [torsorExtClass_ofCoefficientIso, representedH1AddEquiv_torsor]

section CanonicalCoefficient
variable [IsSepClosed K]
variable (L : AbelianSheaf.{u, u + 1} X) (hcoeff : FiniteCoefficient L)

/-- The actual coefficient group chosen only by the precise finite-set-sheaf
representability theorem, with group operations constructed by Yoneda. -/
abbrev finiteCoefficientRepresentation : CoefficientRepresentation L :=
  CoefficientRepresentation.ofFiniteLocallyConstant L hR hcoeff.locally_constant

variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : coefficientFiber s L ≃+ M)
variable (hmark : ∀ (γ : FiberAutGroup s)
    (a : Over.mk s ⟶ (finiteCoefficientRepresentation hR L hcoeff).group.X),
  (finiteCoefficientRepresentation hR L hcoeff).pointMark s mark
      (γ.hom.app (coefficientCover (finiteCoefficientRepresentation hR L hcoeff).group) a) =
    Multiplicative.ofAdd (γ • ((finiteCoefficientRepresentation hR L hcoeff).pointMark s mark
      a).toAdd))

/-- The finite locally constant small-etale Ext H¹/fundamental-group H¹ additive
equivalence. Its marking is on the actual geometric stalk, and its equivariance
condition is literal evaluation of the actual finite-etale fibre automorphisms.
The positive annihilator and invertible level remain displayed in `hcoeff`. -/
def compareH1 : H1Etale X L ≃+ H1 (FiberAutGroup s) M :=
  compareH1WithRepresentation s hA hR L (finiteCoefficientRepresentation hR L hcoeff)
    M ((finiteCoefficientRepresentation hR L hcoeff).pointMark s mark) hmark hcoeff

/-- Every genuine torsor representative computes the canonical arbitrary-L
comparison by the original actual-stalk marking of positive transport. -/
theorem compareH1_torsor_representative (P : Torsor L) (Y : Scheme.FiniteEtale X)
    (e : finiteRepresentedSetSheaf Y ≅ P.carrier) (t : Fiber s Y) :
    compareH1 s hA hR L hcoeff M mark hmark (torsorExtClass P) =
      classOf (FiberAutGroup s) M
        (markedBasedCocycle s (finiteCoefficientRepresentation hR L hcoeff).group M
          ((finiteCoefficientRepresentation hR L hcoeff).pointMark s mark) hmark Y
          ((P.ofCoefficientIso (finiteCoefficientRepresentation hR L
            hcoeff).iso.symm).representedSchemeAction (finiteCoefficientRepresentation hR L
            hcoeff).group Y e) t) :=
  compareH1WithRepresentation_torsor_representative s hA hR L
    (finiteCoefficientRepresentation hR L hcoeff) M
    ((finiteCoefficientRepresentation hR L hcoeff).pointMark s mark) hmark hcoeff P Y e t

end CanonicalCoefficient

end FundamentalGroupComparison
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 293c680448e2afd520d895d41a1897a024c8c110725f3bfe7694e7cf44810e45.
Definitions, hypotheses and universes are retained modulo native names. -/
