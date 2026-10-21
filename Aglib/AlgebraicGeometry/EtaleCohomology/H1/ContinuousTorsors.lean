/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Torsor
public import Aglib.GroupCohomology.H1.Continuous
public import Aglib.GroupCohomology.H1.AffineTorsor

/-!
# Common continuous H¹ representatives of actual finite étale torsors

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The forward cocycle uses the
already constructed natural fibre permutation and unique scheme transport
from FiberTorsorActions. No independent representation or H¹ quotient is
introduced. The convention is γ(t)=c_t(γ)+t, with positive principal change.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite mk)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors
open GroupCohomology.ContinuousH1
universe u
attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom] (Y : Scheme.FiniteEtale X)
variable (τ : TorsorAction A (toUnit Y.obj))
variable {M : Type u} [AddCommGroup M]
variable (mark : (Over.mk s ⟶ A.X) ≃* Multiplicative M)
variable [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (hmark : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X),
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

/-- The common continuous cocycle obtained from actual fibre evaluation at a chosen point. -/
def basedCocycle (t : Fiber s Y) : Cocycle (FiberAutGroup s) M := by
  have hc : Continuous (fun γ : FiberAutGroup s =>
      fibreBasis s A Y τ mark t (γ.hom.app Y t)) := by
    have hcoord : Continuous (fun γ : FiberAutGroup s =>
        PreGaloisCategory.autEmbedding (fiberToFinite s) γ Y) :=
      (continuous_apply Y).comp continuous_induced_dom
    let eval : Aut ((fiberToFinite s).obj Y) → M := fun a =>
      fibreBasis s A Y τ mark t (a.hom t)
    exact (continuous_of_discreteTopology (f := eval)).comp hcoord
  have he (γ : FiberAutGroup s) :
      rho s A Y τ mark t γ 0 = fibreBasis s A Y τ mark t (γ.hom.app Y t) := by
    rw [rho_apply, fibreBasis_symm_zero]
  have hc' : Continuous (fun γ : FiberAutGroup s => rho s A Y τ mark t γ (0 : M)) :=
    hc.congr (fun γ => (he γ).symm)
  refine ⟨⟨(fun γ => rho s A Y τ mark t γ 0), hc'⟩, ?_⟩
  intro γ δ
  change rho s A Y τ mark t (γ * δ) 0 = _
  rw [map_mul]
  change rho s A Y τ mark t γ (rho s A Y τ mark t δ 0) =
    rho s A Y τ mark t γ 0 + γ • rho s A Y τ mark t δ 0
  simpa only [zero_add, MonoidHom.id_apply] using
    rho_affine s A Y τ mark t (MonoidHom.id _) hmark γ 0 (rho s A Y τ mark t δ 0)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- The representative is literal positive transport from t to γ(t). -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem basedCocycle_apply (t : Fiber s Y) (γ : FiberAutGroup s) :
    (basedCocycle s A Y τ mark hmark t).val γ =
      fibreBasis s A Y τ mark t (γ.hom.app Y t) := by
  change rho s A Y τ mark t γ 0 = _
  rw [rho_apply, fibreBasis_symm_zero]

/-- The defining actual scheme-point equation fixes the cocycle sign. -/
theorem basedCocycle_action (t : Fiber s Y) (γ : FiberAutGroup s) :
    τ.act (mark.symm (Multiplicative.ofAdd ((basedCocycle s A Y τ mark hmark t).val γ))) t =
      γ.hom.app Y t := by
  rw [basedCocycle_apply]
  exact (fibreBasis s A Y τ mark t).symm_apply_apply _

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Coordinates at another actual fibre point differ by its old coordinate. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem fibreBasis_change (t t' x : Fiber s Y) :
    fibreBasis s A Y τ mark t' x =
      fibreBasis s A Y τ mark t x - fibreBasis s A Y τ mark t t' := by
  have h := fibreBasis_action s A Y τ mark t
    (mark.symm (Multiplicative.ofAdd (fibreBasis s A Y τ mark t' x))) t'
  have hx : τ.act (mark.symm (Multiplicative.ofAdd (fibreBasis s A Y τ mark t' x))) t' = x :=
    (fibreBasis s A Y τ mark t').symm_apply_apply x
  rw [hx, mark.apply_symm_apply] at h
  change fibreBasis s A Y τ mark t x =
    fibreBasis s A Y τ mark t t' + fibreBasis s A Y τ mark t' x at h
  exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h.symm)

/-- Basepoint change is the positive principal cocycle g·a−a. -/
theorem basedCocycle_change (t t' : Fiber s Y) :
    basedCocycle s A Y τ mark hmark t' = basedCocycle s A Y τ mark hmark t +
      GroupCohomology.ContinuousH1.principal (FiberAutGroup s) M (fibreBasis s A Y τ mark t t')
        := by
  apply GroupCohomology.ContinuousH1.Cocycle.ext
  intro γ
  rw [GroupCohomology.ContinuousH1.Cocycle.add_apply,
    GroupCohomology.ContinuousH1.principal_apply, basedCocycle_apply, basedCocycle_apply,
    fibreBasis_change]
  · have h := rho_affine s A Y τ mark t (MonoidHom.id _) hmark γ 0
      (fibreBasis s A Y τ mark t t')
    rw [zero_add, rho_fibre] at h
    change fibreBasis s A Y τ mark t (γ.hom.app Y t') =
      rho s A Y τ mark t γ 0 + γ • fibreBasis s A Y τ mark t t' at h
    rw [rho_apply, fibreBasis_symm_zero] at h
    rw [h]
    abel

/-- The common continuous H¹ class is independent of the internal point choice. -/
theorem basedCocycle_class_independent (t t' : Fiber s Y) :
    GroupCohomology.ContinuousH1.classOf (FiberAutGroup s) M (basedCocycle s A Y τ mark hmark t') =
      GroupCohomology.ContinuousH1.classOf (FiberAutGroup s) M (basedCocycle s A Y τ mark hmark
        t) := by
  rw [basedCocycle_change, map_add, GroupCohomology.ContinuousH1.classOf_principal, add_zero]

/-- The common continuous H¹ class of a nonempty actual finite étale scheme torsor. -/
def schemeTorsorClass [Nonempty (Fiber s Y)] : GroupCohomology.ContinuousH1.H1 (FiberAutGroup s)
  M :=
  GroupCohomology.ContinuousH1.classOf (FiberAutGroup s) M (basedCocycle s A Y τ mark hmark
    (Classical.choice inferInstance))

/-- Any actual chosen fibre point computes the constructed class. -/
theorem schemeTorsorClass_eq [Nonempty (Fiber s Y)] (t : Fiber s Y) :
    schemeTorsorClass s A Y τ mark hmark =
      GroupCohomology.ContinuousH1.classOf (FiberAutGroup s) M (basedCocycle s A Y τ mark hmark
        t) :=
  basedCocycle_class_independent s A Y τ mark hmark _ _

section Naturality
variable (A' : Grp (Over X)) [IsFinite A'.X.hom] [Etale A'.X.hom] (Y' : Scheme.FiniteEtale X)
variable (τ' : TorsorAction A' (toUnit Y'.obj))
variable {M' : Type u} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
variable [DistribMulAction (FiberAutGroup s) M'] [ContinuousSMul (FiberAutGroup s) M']
variable (mark' : (Over.mk s ⟶ A'.X) ≃* Multiplicative M')
variable (hmark' : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A'.X),
  mark' (γ.hom.app (coefficientCover A') a) = Multiplicative.ofAdd (γ • (mark' a).toAdd))
variable (q : CoefficientMap (FiberAutGroup s) M M')
variable (e : Fiber s Y → Fiber s Y')
variable (he : ∀ (a : M) (t : Fiber s Y),
  e (τ.act (mark.symm (Multiplicative.ofAdd a)) t) =
    τ'.act (mark'.symm (Multiplicative.ofAdd (q a))) (e t))

include he in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- An actual equivariant fibre map carries transport coordinates by its
coefficient map; neither injectivity nor a chosen global section is required. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem fibreBasis_naturality (t x : Fiber s Y) :
    fibreBasis s A' Y' τ' mark' (e t) (e x) = q (fibreBasis s A Y τ mark t x) := by
  have hx := (fibreBasis s A Y τ mark t).symm_apply_apply x
  change τ.act (mark.symm (Multiplicative.ofAdd (fibreBasis s A Y τ mark t x))) t = x at hx
  have hh := he (fibreBasis s A Y τ mark t x) t
  rw [hx] at hh
  rw [hh, fibreBasis_action, fibreBasis_basepoint, mark'.apply_symm_apply, zero_add]
  rfl

include he in
/-- Naturality of the literal representative under compatible actual fibre maps. -/
theorem basedCocycle_naturality
    (hΓ : ∀ (γ : FiberAutGroup s) (t : Fiber s Y), e (γ.hom.app Y t) = γ.hom.app Y' (e t))
    (t : Fiber s Y) :
    basedCocycle s A' Y' τ' mark' hmark' (e t) =
      q.onCocycles (basedCocycle s A Y τ mark hmark t) := by
  apply Cocycle.ext
  intro γ
  rw [CoefficientMap.onCocycles_apply, basedCocycle_apply, basedCocycle_apply, ← hΓ]
  exact fibreBasis_naturality s A Y τ mark A' Y' τ' mark' q e he t _

include he in
/-- The induced map on the one common continuous H¹ is the proved coefficient
map of the actual torsor-fibre class. -/
theorem schemeTorsorClass_naturality [Nonempty (Fiber s Y)] [Nonempty (Fiber s Y')]
    (hΓ : ∀ (γ : FiberAutGroup s) (t : Fiber s Y), e (γ.hom.app Y t) = γ.hom.app Y' (e t)) :
    schemeTorsorClass s A' Y' τ' mark' hmark' =
      q.onH1 (schemeTorsorClass s A Y τ mark hmark) := by
  let t : Fiber s Y := Classical.choice inferInstance
  rw [schemeTorsorClass_eq s A Y τ mark hmark t,
    schemeTorsorClass_eq s A' Y' τ' mark' hmark' (e t),
    basedCocycle_naturality s A Y τ mark hmark A' Y' τ' mark' hmark' q e he hΓ,
    CoefficientMap.onH1_classOf]

end Naturality

section Descend
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.TorsorDescent
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable [Finite M]

/-- A common continuous cocycle descends to an actual finite étale cover. -/
def cocycleCover (c : Cocycle (FiberAutGroup s) M) : Scheme.FiniteEtale X :=
  torsorCover s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c)

/-- The natural finite fibre marking of the descended affine cover. -/
def cocycleFiberEquiv (c : Cocycle (FiberAutGroup s) M) :
    Fiber s (cocycleCover s c) ≃ GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c :=
  torsorFiberEquiv s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c)

/-- The genuine scheme torsor action obtained by descent of the affine action. -/
def cocycleSchemeAction (c : Cocycle (FiberAutGroup s) M) :
    TorsorAction (moduleScheme s M) (toUnit (cocycleCover s c).obj) :=
  schemeTorsorAction s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c) (Multiplicative M)
    (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.multiplicative_compatible c (fun _ _
      => rfl))
    (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.multiplicative_transport c)

/-- The constructed torsor action has the prescribed literal fibre translations. -/
theorem cocycleSchemeAction_fiber (c : Cocycle (FiberAutGroup s) M)
    (a : Over.mk s ⟶ (moduleScheme s M).X) (t : Fiber s (cocycleCover s c)) :
    (cocycleFiberEquiv s c ((cocycleSchemeAction s c).act a t)).val =
      (moduleFiberMulEquiv s M a).toAdd + (cocycleFiberEquiv s c t).val := by
  exact congrArg GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.val
    (schemeTorsorAction_fiber s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c)
      (Multiplicative M)
      (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.multiplicative_compatible c (fun _
        _ => rfl))
      (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.multiplicative_transport c) a t)

/-- The zero coordinate provides an actual geometric point of the descended torsor. -/
def cocycleBasepoint (c : Cocycle (FiberAutGroup s) M) : Fiber s (cocycleCover s c) :=
  (cocycleFiberEquiv s c).symm ⟨0⟩

/-- The ordinary fibre basis of the descended torsor is its original affine coordinate. -/
theorem cocycle_fibreBasis (c : Cocycle (FiberAutGroup s) M)
    (t : Fiber s (cocycleCover s c)) :
    fibreBasis s (moduleScheme s M) (cocycleCover s c) (cocycleSchemeAction s c)
      (moduleFiberMulEquiv s M) (cocycleBasepoint s c) t =
      (cocycleFiberEquiv s c t).val := by
  apply (fibreBasis s (moduleScheme s M) (cocycleCover s c) (cocycleSchemeAction s c)
    (moduleFiberMulEquiv s M) (cocycleBasepoint s c)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (cocycleFiberEquiv s c).injective
  apply GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.ext c
  change (cocycleFiberEquiv s c t).val =
    (cocycleFiberEquiv s c ((cocycleSchemeAction s c).act
      ((moduleFiberMulEquiv s M).symm (Multiplicative.ofAdd
        (cocycleFiberEquiv s c t).val)) (cocycleBasepoint s c))).val
  rw [cocycleSchemeAction_fiber, MulEquiv.apply_symm_apply]
  simp only [cocycleBasepoint, Equiv.apply_symm_apply, add_zero]
  rfl

/-- Extracting the actual geometric displacement recovers the starting common cocycle. -/
theorem basedCocycle_cocycleSchemeAction (c : Cocycle (FiberAutGroup s) M) :
    basedCocycle s (moduleScheme s M) (cocycleCover s c) (cocycleSchemeAction s c)
      (moduleFiberMulEquiv s M) (moduleFiber_action s M) (cocycleBasepoint s c) = c := by
  apply Cocycle.ext
  intro γ
  rw [basedCocycle_apply, cocycle_fibreBasis]
  change (torsorFiberEquiv s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c)
    (γ.hom.app (torsorCover s (GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint c))
      (cocycleBasepoint s c))).val = _
  rw [torsorFiber_action]
  change (γ • ((cocycleFiberEquiv s c) ((cocycleFiberEquiv s c).symm ⟨0⟩))).val = _
  rw [Equiv.apply_symm_apply,
    GroupCohomology.ContinuousH1.AffineTorsors.AffinePoint.displacement_zero]

end Descend

end AlgebraicGeometry.Scheme.EtaleCohomology.ContinuousTorsors

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ad15cb737883d57719047d478d8fbf1e0b41c2593a580ea399c63bc1d3fbe2b2.
Definitions, hypotheses and universes are retained modulo native names. -/
