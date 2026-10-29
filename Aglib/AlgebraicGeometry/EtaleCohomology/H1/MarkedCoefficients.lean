/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorClassification
public import Aglib.GroupCohomology.H1.Continuous.CoefficientTransport

/-!
# Marked descent of actual finite coefficient group schemes

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The actual GC+FF classification
and fibre faithfulness construct group-scheme morphisms from compatible
finite-fibre group maps. In particular, a genuine equivariant fibre marking
identifies an actual finite coefficient group scheme with module descent.
All point-marking formulas are retained, including universe transports.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
namespace AlgebraicGeometry.Scheme.EtaleCohomology.MarkedCoefficients
open SchemeTorsorClassification
universe u v
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian
variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- Fibre faithfulness upgrades genuine point-group laws to actual group-scheme laws. -/
theorem isMonHom_of_fiber (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (f : A.X ⟶ B.X) (hone : (1 : Over.mk s ⟶ A.X) ≫ f = 1)
    (hmul : ∀ a b : Over.mk s ⟶ A.X, (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f := by
  let : IsFinite (𝟙_ (Over X)).hom := (𝟙_ (Scheme.FiniteEtale X)).property.1
  let : Etale (𝟙_ (Over X)).hom := (𝟙_ (Scheme.FiniteEtale X)).property.2
  let : IsFinite (A.X ⊗ A.X).hom := (coefficientCover A ⊗ coefficientCover A).property.1
  let : Etale (A.X ⊗ A.X).hom := (coefficientCover A ⊗ coefficientCover A).property.2
  constructor
  · apply finiteEtale_hom_ext s
    intro p
    have hp : p = toUnit (Over.mk s) := toUnit_unique _ _
    subst p
    exact (Category.assoc _ _ _).symm.trans hone
  · apply finiteEtale_hom_ext s
    intro p
    rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    exact hmul _ _

/-- Actual equivariant finite-fibre group maps descend to actual group-scheme maps. -/
def descendFiberGroupHom (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (q : (Over.mk s ⟶ A.X) →* (Over.mk s ⟶ B.X))
    (hq : ∀ (γ : FiberAutGroup s) a,
      q (γ.hom.app (coefficientCover A) a) = γ.hom.app (coefficientCover B) (q a)) : A ⟶ B := by
  let f := descendFiberMap s (Y := coefficientCover A) (Z := coefficientCover B) q hq
  have hf (a : Over.mk s ⟶ A.X) : a ≫ f = q a :=
    descendFiberMap_fiber s (Y := coefficientCover A) (Z := coefficientCover B) q hq a
  letI : IsMonHom f := isMonHom_of_fiber s A B f
    ((hf 1).trans q.map_one)
    (fun a b => (hf (a * b)).trans ((q.map_mul a b).trans
      (congrArg₂ (· * ·) (hf a).symm (hf b).symm)))
  exact Grp.homMk f

/-- Descent has the prescribed literal effect on geometric coefficient points. -/
theorem descendFiberGroupHom_fiber (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (q : (Over.mk s ⟶ A.X) →* (Over.mk s ⟶ B.X))
    (hq : ∀ (γ : FiberAutGroup s) a,
      q (γ.hom.app (coefficientCover A) a) = γ.hom.app (coefficientCover B) (q a))
    (a : Over.mk s ⟶ A.X) : a ≫ (descendFiberGroupHom s A B q hq).hom.hom = q a :=
  descendFiberMap_fiber s (Y := coefficientCover A) (Z := coefficientCover B) q hq a

/-- An equivariant fibre group equivalence constructs an actual Grp isomorphism. -/
def descendFiberGroupIso (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (e : (Over.mk s ⟶ A.X) ≃* (Over.mk s ⟶ B.X))
    (he : ∀ (γ : FiberAutGroup s) a,
      e (γ.hom.app (coefficientCover A) a) = γ.hom.app (coefficientCover B) (e a)) : A ≅ B := by
  let d := descendFiberIso s (Y := coefficientCover A) (Z := coefficientCover B) e.toEquiv he
  have hd_apply (a : Over.mk s ⟶ A.X) : a ≫ d.hom = e a :=
    descendFiberIso_hom_fiber s (Y := coefficientCover A) (Z := coefficientCover B) e.toEquiv he a
  have hd : IsMonHom d.hom := isMonHom_of_fiber s A B d.hom
    (by rw [hd_apply]; exact e.map_one)
    (by intro a b; rw [hd_apply, hd_apply, hd_apply]; exact e.map_mul a b)
  exact Grp.mkIso d hd.one_hom hd.mul_hom

/-- The actual descended group isomorphism has exactly the given fibre marking. -/
theorem descendFiberGroupIso_fiber (A B : Grp (Over X))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (e : (Over.mk s ⟶ A.X) ≃* (Over.mk s ⟶ B.X))
    (he : ∀ (γ : FiberAutGroup s) a,
      e (γ.hom.app (coefficientCover A) a) = γ.hom.app (coefficientCover B) (e a))
    (a : Over.mk s ⟶ A.X) : a ≫ (descendFiberGroupIso s A B e he).hom.hom.hom = e a :=
  descendFiberIso_hom_fiber s (Y := coefficientCover A) (Z := coefficientCover B) e.toEquiv he a

section Marking
variable (H : Grp (Over X)) [IsFinite H.X.hom] [Etale H.X.hom]
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

/-- The composite of the two genuine markings is the coefficient-fibre equivalence. -/
def moduleMarkedFiberEquiv :
    (Over.mk s ⟶ (moduleScheme s M).X) ≃* (Over.mk s ⟶ H.X) :=
  (moduleFiberMulEquiv s M).trans mark.symm

include hmark in
/-- The marked fibre equivalence respects actual natural fibre evaluation. -/
theorem moduleMarkedFiberEquiv_equivariant (γ : FiberAutGroup s)
    (a : Over.mk s ⟶ (moduleScheme s M).X) :
    moduleMarkedFiberEquiv s H M mark (γ.hom.app (coefficientCover (moduleScheme s M)) a) =
      γ.hom.app (coefficientCover H) (moduleMarkedFiberEquiv s H M mark a) := by
  apply mark.injective
  change mark (mark.symm (moduleFiberMulEquiv s M _)) = _
  rw [mark.apply_symm_apply]
  calc
    _ = Multiplicative.ofAdd (γ • (moduleFiberMulEquiv s M a).toAdd) := moduleFiber_action s M γ a
    _ = _ := ?_
  rw [hmark]
  change Multiplicative.ofAdd (γ • (moduleFiberMulEquiv s M a).toAdd) =
    Multiplicative.ofAdd (γ • (mark (mark.symm (moduleFiberMulEquiv s M a))).toAdd)
  rw [mark.apply_symm_apply]

/-- A marked actual finite coefficient group is canonically its module descent. -/
def moduleGroupIso : moduleScheme s M ≅ H :=
  descendFiberGroupIso s (moduleScheme s M) H (moduleMarkedFiberEquiv s H M mark)
    (moduleMarkedFiberEquiv_equivariant s H M mark hmark)

/-- The group-scheme identification preserves the original marking literally. -/
theorem moduleGroupIso_marking (a : Over.mk s ⟶ (moduleScheme s M).X) :
    mark (a ≫ (moduleGroupIso s H M mark hmark).hom.hom.hom) = moduleFiberMulEquiv s M a := by
  rw [moduleGroupIso, descendFiberGroupIso_fiber]
  exact mark.apply_symm_apply _

end Marking

/-- Actual group-scheme isomorphisms induce actual additive-sheaf isomorphisms. -/
def representedSheafIso {A B : Grp (Over X)} [IsCommMonObj A.X] [IsCommMonObj B.X]
    (e : A ≅ B) : representedSheaf A ≅ representedSheaf B where
  hom := representedSheafMap e.hom
  inv := representedSheafMap e.inv
  hom_inv_id := by rw [← representedSheafMap_comp, e.hom_inv_id, representedSheafMap_id]
  inv_hom_id := by rw [← representedSheafMap_comp, e.inv_hom_id, representedSheafMap_id]

/-- The marked descent comparison is an actual additive sheaf isomorphism. -/
def moduleSheafIso (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
    (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
    (hmark : ∀ (γ : FiberAutGroup s) a,
      mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd)) :
    moduleSheaf s M ≅ representedSheaf H := representedSheafIso (moduleGroupIso s H M mark hmark)

section SmallFibre
variable (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]

/-- A small-universe coefficient module whose elements are actual geometric
points of the represented coefficient group. -/
def PointModule := Additive (Over.mk s ⟶ H.X)

instance pointModuleAddCommGroup : AddCommGroup (PointModule s H) :=
  inferInstanceAs (AddCommGroup (Additive (Over.mk s ⟶ H.X)))

instance pointModuleFinite : Finite (PointModule s H) :=
  Finite.of_equiv ((fiberToFinite s).obj (coefficientCover H)) (Equiv.refl _)

instance pointModuleTopologicalSpace : TopologicalSpace (PointModule s H) := ⊥
instance pointModuleDiscreteTopology : DiscreteTopology (PointModule s H) := ⟨rfl⟩

/-- The identity point marking makes the small-universe transport explicit. -/
def pointModuleMark : (Over.mk s ⟶ H.X) ≃* Multiplicative (PointModule s H) where
  toFun a := Multiplicative.ofAdd (Additive.ofMul a)
  invFun a := a.toAdd.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ H.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover H) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

/-- The genuine original marking identifies the small point module with any
finite marked coefficient universe. -/
def pointModuleEquiv : PointModule s H ≃+ M := mark.toAdditiveLeft

/-- Transport of the linear action through the actual marking. Its evaluation
formula below identifies it with actual fibre automorphisms. -/
@[instance_reducible] def pointModuleAction : DistribMulAction (FiberAutGroup s) (PointModule s
  H) :=
  let e := pointModuleEquiv s H M mark
  { e.toEquiv.mulAction (FiberAutGroup s) with
    smul_zero γ := by change e.symm (γ • e 0) = 0; simp
    smul_add γ a b := by
      change e.symm (γ • e (a + b)) = e.symm (γ • e a) + e.symm (γ • e b)
      simp [smul_add] }

set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- The transported action is jointly continuous for the actual evaluation topology. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pointModuleContinuousSMul :
    letI := pointModuleAction s H M mark
    ContinuousSMul (FiberAutGroup s) (PointModule s H) := by
  let := pointModuleAction s H M mark
  let e := pointModuleEquiv s H M mark
  exact ⟨(continuous_of_discreteTopology (f := e.symm)).comp
    (continuous_fst.smul ((continuous_of_discreteTopology (f := e)).comp continuous_snd))⟩

include hmark in
set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- The small action is actual evaluation, rather than an independently chosen action. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pointModuleAction_evaluation (γ : FiberAutGroup s) (a : Over.mk s ⟶ H.X) :
    letI := pointModuleAction s H M mark
    γ • (show PointModule s H from Additive.ofMul a) =
      (show PointModule s H from Additive.ofMul (γ.hom.app (coefficientCover H) a)) := by
  let := pointModuleAction s H M mark
  apply (pointModuleEquiv s H M mark).injective
  change (pointModuleEquiv s H M mark)
    ((pointModuleEquiv s H M mark).symm (γ • (mark a).toAdd)) =
      (mark (γ.hom.app (coefficientCover H) a)).toAdd
  rw [AddEquiv.apply_symm_apply]
  exact (congrArg Multiplicative.toAdd (hmark γ a)).symm

include hmark in
/-- The identity marking is equivariant for literal actual fibre evaluation. -/
theorem pointModuleMark_equivariant :
    letI := pointModuleAction s H M mark
    ∀ (γ : FiberAutGroup s) a,
      pointModuleMark s H (γ.hom.app (coefficientCover H) a) =
        Multiplicative.ofAdd (γ • (pointModuleMark s H a).toAdd) := by
  let := pointModuleAction s H M mark
  intro γ a
  exact congrArg Multiplicative.ofAdd (pointModuleAction_evaluation s H M mark hmark γ a).symm

/-- The actual represented sheaf is identified with descent of its small
point module. This is the proved finite-universe bridge for comparison. -/
def pointModuleSheafIso :
    letI := pointModuleAction s H M mark
    letI := pointModuleContinuousSMul s H M mark
    moduleSheaf s (PointModule s H) ≅ representedSheaf H := by
  letI := pointModuleAction s H M mark
  letI := pointModuleContinuousSMul s H M mark
  exact moduleSheafIso s H (PointModule s H) (pointModuleMark s H)
    (pointModuleMark_equivariant s H M mark hmark)

end SmallFibre

section CommonH1Transport
open GroupCohomology.ContinuousH1
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {B D : Type*} [AddCommGroup B] [AddCommGroup D]
variable [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] [DiscreteTopology D]
variable [DistribMulAction G B] [ContinuousSMul G B] [DistribMulAction G D] [ContinuousSMul G D]
variable (e : B ≃+ D) (he : ∀ (γ : G) b, e (γ • b) = γ • e b)

/-- A genuine equivariant additive marking, with its automatic discrete continuity. -/
def coefficientMapOfEquiv : CoefficientMap G B D :=
  GroupCohomology.ContinuousH1.CoefficientTransport.coefficientMapOfEquiv e he

include he in
set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- The inverse marking is equivariant as well. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem coefficientEquiv_symm_equivariant (γ : G) (d : D) :
    e.symm (γ • d) = γ • e.symm d :=
  GroupCohomology.ContinuousH1.CoefficientTransport.coefficientEquiv_symm_equivariant e he γ d

/-- Proved coefficient-universe transport of the one existing continuous H¹.
Its cocycle map is literal postcomposition with the supplied marking. -/
def coefficientH1Equiv : H1 G B ≃+ H1 G D :=
  GroupCohomology.ContinuousH1.CoefficientTransport.coefficientH1Equiv e he

/-- The universe/marking bridge does not change the cocycle beyond its stated
coefficient map. -/
theorem coefficientH1Equiv_classOf (c : Cocycle G B) :
    coefficientH1Equiv e he (classOf G B c) =
      classOf G D ((coefficientMapOfEquiv e he).onCocycles c) :=
  GroupCohomology.ContinuousH1.CoefficientTransport.coefficientH1Equiv_classOf e he c

end CommonH1Transport

end AlgebraicGeometry.Scheme.EtaleCohomology.MarkedCoefficients

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 937d72ec86a82f709edd6efe5cd020187e4b55f316ec0c00aa1a627fe4a8bdbe.
Definitions, hypotheses and universes are retained modulo native names. -/
