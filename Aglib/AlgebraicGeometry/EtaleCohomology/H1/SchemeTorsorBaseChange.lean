/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorAdjunction
public import Aglib.AlgebraicGeometry.Sites.EtaleTopos
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedTorsor
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ContinuousTorsors
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.GroupScheme

/-!
# Actual scheme-torsor pullback and its cohomological restriction

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Scheme pullback of the action is
constructed on every test scheme through the actual Over adjunction. Its
represented section map supplies the ordinary adjoint torsor map, and the
canonical coefficient-unit identity fixes the actual H¹ pullback square.
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
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality
namespace AlgebraicGeometry.Scheme.EtaleCohomology.SchemeTorsorBaseChange
universe u
attribute [local instance] Over.cartesianMonoidalCategory coverCartesian hasSheafifyLarge
variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- The actual pullback universal property on arbitrary scheme-valued tests. -/
abbrev pullbackSectionEquiv (T : Over S) (Y : Over X) :
    ((Over.map f).obj T ⟶ Y) ≃ (T ⟶ (Over.pullback f).obj Y) :=
  (Over.mapPullbackAdj f).homEquiv T Y

/-- The coefficient section comparison preserves multiplication on all tests. -/
def pullbackSectionMulEquiv (T : Over S) (A : Grp (Over X)) :
    ((Over.map f).obj T ⟶ A.X) ≃* (T ⟶ (baseChangedGroup f A).X) where
  __ := pullbackSectionEquiv f T A.X
  map_mul' a b := by
    let : GrpObj ((Over.pullback f).obj A.X) := (baseChangedGroup f A).grp
    change (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map (a * b) =
      ((Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map a) *
        ((Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map b)
    rw [(Over.pullback f).map_mul, comp_mul]

/-- Naturality of the inverse section comparison in arbitrary test schemes. -/
theorem pullbackSectionEquiv_symm_naturality {T U : Over S} (g : T ⟶ U) (Y : Over X)
    (x : U ⟶ (Over.pullback f).obj Y) :
    (pullbackSectionEquiv f T Y).symm (g ≫ x) =
      (Over.map f).map g ≫ (pullbackSectionEquiv f U Y).symm x :=
  (Over.mapPullbackAdj f).homEquiv_naturality_left_symm g x

/-- Pullback of a morphism corresponds to its composition with the actual counit. -/
theorem pullbackSectionEquiv_symm_map {U Y : Over X} (x : U ⟶ Y) :
    (pullbackSectionEquiv f ((Over.pullback f).obj U) Y).symm ((Over.pullback f).map x) =
      (Over.mapPullbackAdj f).counit.app U ≫ x := by
  change (Over.map f).map ((Over.pullback f).map x) ≫ (Over.mapPullbackAdj f).counit.app Y = _
  exact (Over.mapPullbackAdj f).counit.naturality x

variable (A : Grp (Over X)) (Y : Scheme.FiniteEtale X) (τ : TorsorAction A (toUnit Y.obj))

/-- Pullback of a genuine scheme torsor, with the action and unique transport
constructed on every scheme over S. -/
def pullbackSchemeAction :
    TorsorAction (baseChangedGroup f A) (toUnit ((baseChange f).obj Y).obj) where
  act {T} a x := pullbackSectionEquiv f T Y.obj
    (τ.act ((pullbackSectionMulEquiv f T A).symm a) ((pullbackSectionEquiv f T Y.obj).symm x))
  naturality {T U} g a x := by
    apply (pullbackSectionEquiv f T Y.obj).symm.injective
    rw [pullbackSectionEquiv_symm_naturality, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      τ.naturality]
    congr 1
  one_act {T} x := by
    rw [map_one, τ.one_act, Equiv.apply_symm_apply]
  mul_act {T} a b x := by
    rw [map_mul, τ.mul_act]
    congr 1
    rw [Equiv.symm_apply_apply]
  over _ _ := toUnit_unique _ _
  transport {T} x y _ := by
    obtain ⟨a, ha, hu⟩ := τ.transport ((pullbackSectionEquiv f T Y.obj).symm x)
      ((pullbackSectionEquiv f T Y.obj).symm y) (toUnit_unique _ _)
    refine ⟨pullbackSectionMulEquiv f T A a, ?_, ?_⟩
    · exact (congrArg (fun b => pullbackSectionEquiv f T Y.obj
        (τ.act b ((pullbackSectionEquiv f T Y.obj).symm x)))
          ((pullbackSectionMulEquiv f T A).symm_apply_apply a)).trans
        ((congrArg (pullbackSectionEquiv f T Y.obj) ha).trans
          ((pullbackSectionEquiv f T Y.obj).apply_symm_apply y))
    · intro b hb
      apply (pullbackSectionMulEquiv f T A).symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply hu
      exact (pullbackSectionEquiv f T Y.obj).injective (hb.trans
        ((pullbackSectionEquiv f T Y.obj).apply_symm_apply y).symm)

/-- Pullback of actual sections intertwines the actual scheme actions. -/
theorem pullbackSchemeAction_map {U : Over X} (a : U ⟶ A.X) (x : U ⟶ Y.obj) :
    (pullbackSchemeAction f A Y τ).act ((Over.pullback f).map a) ((Over.pullback f).map x) =
      (Over.pullback f).map (τ.act a x) := by
  apply (pullbackSectionEquiv f ((Over.pullback f).obj U) Y.obj).symm.injective
  change (pullbackSectionEquiv f _ Y.obj).symm
      ((pullbackSectionEquiv f _ Y.obj) (τ.act _ _)) = _
  rw [Equiv.symm_apply_apply]
  change τ.act ((pullbackSectionEquiv f ((Over.pullback f).obj U) A.X).symm
    ((Over.pullback f).map a)) ((pullbackSectionEquiv f ((Over.pullback f).obj U) Y.obj).symm
      ((Over.pullback f).map x)) = _
  simp only [pullbackSectionEquiv_symm_map, τ.naturality]

/-- Actual fibre pullback intertwines translation with the canonical
multiplicative coefficient-point pullback, fixing the positive convention. -/
theorem pullbackSchemeAction_fiber {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (a : Over.mk (s ≫ f) ⟶ A.X) (x : Fiber (s ≫ f) Y) :
    (pullbackSchemeAction f A Y τ).act (pullbackFiberMulEquiv f s A a)
      (fiberBaseChangeEquiv f s Y x) = fiberBaseChangeEquiv f s Y (τ.act a x) := by
  change (pullbackSectionEquiv f (Over.mk s) Y.obj)
    (τ.act ((pullbackSectionMulEquiv f (Over.mk s) A).symm
      (pullbackSectionMulEquiv f (Over.mk s) A a))
      ((pullbackSectionEquiv f (Over.mk s) Y.obj).symm
        (pullbackSectionEquiv f (Over.mk s) Y.obj x))) = _
  rw [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-- Surjectivity of an actual cover is preserved by its actual scheme pullback. -/
instance baseChange_surjective [Surjective Y.obj.hom] :
    Surjective ((baseChange f).obj Y).obj.hom := by
  change Surjective (pullback.snd Y.obj.hom f)
  infer_instance

instance baseChangedGroup_finite [IsFinite A.X.hom] : IsFinite (baseChangedGroup f A).X.hom := by
  change IsFinite (pullback.snd A.X.hom f)
  infer_instance

section RepresentedSheaves
variable [IsCommMonObj A.X]

/-- Scheme-theoretic pullback of torsor sections defines an actual set-sheaf map. -/
def representedCarrierUnit : (finiteRepresentedSetSheaf Y : Scheme.EtaleTopos X) ⟶
    (Topos.GeometricMorphism.directImage (Scheme.etaleToposMorphism f)).obj
      (finiteRepresentedSetSheaf ((baseChange f).obj Y) : Scheme.EtaleTopos S) where
  hom := {
    app U := TypeCat.ofHom (fun t => ULift.up ((Over.pullback f).map t.down))
    naturality {U V} g := by
      ext t
      exact congrArg ULift.up ((Over.pullback f).map_comp _ _) }

/-- The topos carrier map retains the original scheme-theoretic section pullback. -/
theorem representedCarrierUnit_app (U : X.Etaleᵒᵖ)
    (t : (finiteRepresentedSetSheaf Y).obj.obj U) :
    (representedCarrierUnit f Y).hom.app U t =
      ULift.up ((Over.pullback f).map t.down) := rfl

/-- The canonical represented section maps form a genuine adjoint torsor map. -/
def representedTorsorAdjointHom [Surjective Y.obj.hom] :
    Torsor.AdjointHom f (representedCoefficientUnit f A)
      (torsorOfSchemeAction A Y τ)
      (torsorOfSchemeAction (baseChangedGroup f A) ((baseChange f).obj Y)
        (pullbackSchemeAction f A Y τ)) where
  map := representedCarrierUnit f Y
  equivariant _U a t := congrArg ULift.up (pullbackSchemeAction_map f A Y τ a.down.toMul
    t.down).symm

section ExtClass
universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Actual scheme torsor pullback has the actual contravariant H¹ class, with
coefficient transport by the canonical represented-sheaf isomorphism. -/
theorem torsorExtClass_pullbackSchemeAction [Etale A.X.hom] [Surjective Y.obj.hom] :
    coefficientMap (representedSheafBaseChangeIso f A).hom
      (h1Pullback f (representedSheaf A) (torsorExtClass (torsorOfSchemeAction A Y τ))) =
    torsorExtClass (torsorOfSchemeAction (baseChangedGroup f A) ((baseChange f).obj Y)
      (pullbackSchemeAction f A Y τ)) := by
  have h := torsorExtClass_adjunction f (representedTorsorAdjointHom f A Y τ)
  change coefficientMap (((inverseImageAdjunction f).homEquiv _ _).symm
    (representedCoefficientUnit f A)) _ = _ at h
  rw [representedCoefficientUnit_adjoint] at h
  exact h

end ExtClass
end RepresentedSheaves
section Monodromy
open ContinuousTorsors
open GroupCohomology.ContinuousH1
variable {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
variable [IsFinite A.X.hom] [Etale A.X.hom]
variable {M : Type u} [AddCommGroup M]
variable (mark : (Over.mk (s ≫ f) ⟶ A.X) ≃* Multiplicative M)

/-- The coefficient marking after pullback is the original marking composed
with the inverse of the actual multiplicative pullback-fibre equivalence. -/
def pullbackFiberMark : (Over.mk s ⟶ (baseChangedGroup f A).X) ≃* Multiplicative M :=
  (pullbackFiberMulEquiv f s A).symm.trans mark

set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- Actual positive transport is unchanged in the canonical pulled-back fibre coordinates. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem fibreBasis_pullback (t x : Fiber (s ≫ f) Y) :
    fibreBasis s (baseChangedGroup f A) ((baseChange f).obj Y) (pullbackSchemeAction f A Y τ)
      (pullbackFiberMark f A s mark) (fiberBaseChangeEquiv f s Y t) (fiberBaseChangeEquiv f s Y x) =
        fibreBasis (s ≫ f) A Y τ mark t x := by
  have ht := transport_unique s (baseChangedGroup f A) ((baseChange f).obj Y)
    (pullbackSchemeAction f A Y τ) (fiberBaseChangeEquiv f s Y t) (fiberBaseChangeEquiv f s Y x)
    (pullbackFiberMulEquiv f s A (transport (s ≫ f) A Y τ t x)) (by
      rw [pullbackSchemeAction_fiber, transport_act])
  change (pullbackFiberMark f A s mark
    (transport s (baseChangedGroup f A) ((baseChange f).obj Y) (pullbackSchemeAction f A Y τ)
      (fiberBaseChangeEquiv f s Y t) (fiberBaseChangeEquiv f s Y x))).toAdd = _
  rw [← ht]
  simp only [pullbackFiberMark, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- Nonempty actual fibres remain nonempty under their canonical pullback equivalence. -/
instance pullbackFiber_nonempty [Nonempty (Fiber (s ≫ f) Y)] :
    Nonempty (Fiber s ((baseChange f).obj Y)) :=
  ⟨fiberBaseChangeEquiv f s Y (Classical.choice inferInstance)⟩

variable [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (s ≫ f)) M] [ContinuousSMul (FiberAutGroup (s ≫ f)) M]
variable (hmark : ∀ (γ : FiberAutGroup (s ≫ f)) (a : Over.mk (s ≫ f) ⟶ A.X),
  mark (γ.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))

include hmark in
set_option linter.unusedSectionVars false in
-- Preserve the original supplied hypotheses and binder order.
/-- The canonical pulled-back coefficient marking has exactly the restricted
linear action along the actual induced fibre-group homomorphism. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pullbackFiberMark_equivariant :
    letI := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
    ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ (baseChangedGroup f A).X),
      pullbackFiberMark f A s mark (γ.hom.app (coefficientCover (baseChangedGroup f A)) a) =
        Multiplicative.ofAdd (γ • (pullbackFiberMark f A s mark a).toAdd) := by
  let := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
  intro γ a
  change mark ((fiberBaseChangeEquiv f s (coefficientCover A)).symm
      (γ.hom.app ((baseChange f).obj (coefficientCover A)) a)) =
    Multiplicative.ofAdd ((inducedGroupHom f s γ) •
      (mark ((fiberBaseChangeEquiv f s (coefficientCover A)).symm a)).toAdd)
  rw [fiberBaseChange_equivariant]
  exact hmark _ _

/-- Literal cocycles of actual pulled-back scheme torsors are restrictions
along the actual continuous fibre-group map, with the canonical coefficient marking. -/
theorem basedCocycle_pullback (t : Fiber (s ≫ f) Y) :
    letI := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
    letI := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
    basedCocycle s (baseChangedGroup f A) ((baseChange f).obj Y) (pullbackSchemeAction f A Y τ)
      (pullbackFiberMark f A s mark) (pullbackFiberMark_equivariant f A s mark hmark)
      (fiberBaseChangeEquiv f s Y t) =
    restrictionCocycles M (inducedGroupHom f s) (basedCocycle (s ≫ f) A Y τ mark hmark t) := by
  let := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
  let := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
  apply Cocycle.ext
  intro γ
  rw [restrictionCocycles_apply, basedCocycle_apply, basedCocycle_apply]
  have he : γ.hom.app ((baseChange f).obj Y) (fiberBaseChangeEquiv f s Y t) =
      fiberBaseChangeEquiv f s Y ((inducedGroupHom f s γ).hom.app Y t) := by
    apply (fiberBaseChangeEquiv f s Y).symm.injective
    rw [Equiv.symm_apply_apply, fiberBaseChange_equivariant, Equiv.symm_apply_apply]
  rw [he, fibreBasis_pullback]

/-- The same restriction identity holds in the one common continuous H¹,
independently of the internal choice of fibre point. -/
theorem schemeTorsorClass_pullback [Nonempty (Fiber (s ≫ f) Y)] :
    letI := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
    letI := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
    schemeTorsorClass s (baseChangedGroup f A) ((baseChange f).obj Y) (pullbackSchemeAction f A Y τ)
      (pullbackFiberMark f A s mark) (pullbackFiberMark_equivariant f A s mark hmark) =
    restriction M (inducedGroupHom f s) (schemeTorsorClass (s ≫ f) A Y τ mark hmark) := by
  let := GroupCohomology.ContinuousH1.restrictedAction M (inducedGroupHom f s)
  let := GroupCohomology.ContinuousH1.restrictedAction_continuous M (inducedGroupHom f s)
  let t : Fiber (s ≫ f) Y := Classical.choice inferInstance
  rw [schemeTorsorClass_eq (s ≫ f) A Y τ mark hmark t,
    schemeTorsorClass_eq s (baseChangedGroup f A) ((baseChange f).obj Y)
      (pullbackSchemeAction f A Y τ) (pullbackFiberMark f A s mark)
      (pullbackFiberMark_equivariant f A s mark hmark) (fiberBaseChangeEquiv f s Y t),
    restriction_classOf, basedCocycle_pullback]

end Monodromy
end AlgebraicGeometry.Scheme.EtaleCohomology.SchemeTorsorBaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 1d69165703f75c3d75739f144ad4dea42338dc0989fa53527274d623ba95edda.
Definitions, hypotheses and universes are retained modulo native names. -/
