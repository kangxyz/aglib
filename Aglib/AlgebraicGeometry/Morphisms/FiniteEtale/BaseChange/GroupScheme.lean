/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Classification

/-!
# Actual coefficient group schemes commute with base change

Source: the coefficient pullback compatibility needed in
`K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

For an actual morphism `f : S ⟶ X` and a field-valued point `s` of `S`, this
module compares the actual pullback of the coefficient group scheme descended
at `s ≫ f` with descent at `s` of the restricted coefficient action. The
classification comparison and the proved multiplicative fibre markings
construct a cover isomorphism. Preservation of unit and multiplication is
proved on fibres and then as equalities of scheme morphisms by faithfulness.
The final result is an isomorphism in `Grp (Over S)`, with an explicit marking
formula, rather than only an isomorphism of point groups.

The retained inputs are exactly the standard Galois-category and fibre-functor
classes for both actual finite-etale scheme categories, together with a finite
discrete group with a continuous action of the actual target fibre group.
The coefficient group may lie in a different universe from the schemes.
Neither a group-preservation certificate nor a coefficient pullback isomorphism
is an input. Verification of the scheme Galois-category classes, rational
origins, geometric connectedness, and coefficient torsor transport remain
outside this subset.

Frozen inputs: `ClassificationNaturality.lean` SHA256
`b42fa423daa3865c6c6832ca02757e2f59c66f1eed0ada955e6a8b9609ededc0` and
`GroupDescent.lean` SHA256
`7d198fddef147ce2e7d8b8bf030e8bac7b3a698fa46f9c50b2a3b0308bbeecaf`.
Each declaration's source pointer uses the module source basis above and
covers this coefficient base-change subset only.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberToFinite fiberToFiniteBaseChangeIso forget)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality

namespace AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange

universe u v

attribute [local instance] Over.cartesianMonoidalCategory GroupDescent.coverCartesian

variable {S X : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)

/-- The canonical point-fibre equivalence for pullback of an actual group
object preserves multiplication, for the coefficient transport subset of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def pullbackFiberMulEquiv (A : Grp (Over X)) :
    (Over.mk (s ≫ f) ⟶ A.X) ≃*
      (Over.mk s ⟶ ((Over.pullback f).mapGrp.obj A).X) where
  __ := (Over.mapPullbackAdj f).homEquiv (Over.mk s) A.X
  map_mul' p q := by
    let : GrpObj ((Over.pullback f).obj A.X) := ((Over.pullback f).mapGrp.obj A).grp
    change (Over.mapPullbackAdj f).unit.app (Over.mk s) ≫
        (Over.pullback f).map (p * q) =
      ((Over.mapPullbackAdj f).unit.app (Over.mk s) ≫ (Over.pullback f).map p) *
        ((Over.mapPullbackAdj f).unit.app (Over.mk s) ≫ (Over.pullback f).map q)
    rw [(Over.pullback f).map_mul, MonObj.comp_mul]

variable (M : Type v) [Group M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (FiberAutGroup (s ≫ f)) M]
  [ContinuousSMul (FiberAutGroup (s ≫ f)) M]

/-- Restriction of the coefficient group action along the actual continuous
fibre-group map in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[instance_reducible] def restrictedAction : MulDistribMulAction (FiberAutGroup s) M :=
  MulDistribMulAction.compHom M (inducedGroupHom f s).toMonoidHom

omit [Finite M] [DiscreteTopology M] in
/-- The restricted coefficient action is jointly continuous in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem restrictedContinuousSMul :
    letI := restrictedAction f s M
    ContinuousSMul (FiberAutGroup s) M := by
  let := restrictedAction f s M
  exact ⟨(continuous_smul (M := FiberAutGroup (s ≫ f)) (X := M)).comp
    (((inducedGroupHom f s).continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩

variable [GaloisCategory (Scheme.FiniteEtale S)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (s ≫ f))]

/-- The actual coefficient cover descended from the restricted action, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedGroupCover : Scheme.FiniteEtale S := by
  letI := restrictedAction f s M
  letI := restrictedContinuousSMul f s M
  exact groupCover s M

/-- The actual coefficient group scheme descended from the restricted
action, for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedGroupScheme : Grp (Over S) := by
  letI := restrictedAction f s M
  letI := restrictedContinuousSMul f s M
  exact groupScheme s M

/-- The restricted coefficient scheme is finite in the coefficient
transport subset of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
instance restrictedGroupScheme_finite : IsFinite (restrictedGroupScheme f s M).X.hom := by
  let := restrictedAction f s M
  let := restrictedContinuousSMul f s M
  exact groupScheme_finite s M

/-- The restricted coefficient scheme is etale in the coefficient
transport subset of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
instance restrictedGroupScheme_etale : Etale (restrictedGroupScheme f s M).X.hom := by
  let := restrictedAction f s M
  let := restrictedContinuousSMul f s M
  exact groupScheme_etale s M

/-- The actual pulled-back coefficient group scheme is finite in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
instance pullbackGroupScheme_finite :
    IsFinite ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X.hom := by
  let : IsFinite (groupScheme (s ≫ f) M).X.hom := groupScheme_finite (s ≫ f) M
  change IsFinite (pullback.snd (groupScheme (s ≫ f) M).X.hom f)
  infer_instance

/-- The actual pulled-back coefficient group scheme is etale in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
instance pullbackGroupScheme_etale :
    Etale ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X.hom := by
  let : Etale (groupScheme (s ≫ f) M).X.hom := groupScheme_etale (s ≫ f) M
  change Etale (pullback.snd (groupScheme (s ≫ f) M).X.hom f)
  infer_instance

/-- The restricted coefficient scheme has its actual multiplicative fibre
marking in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedGroupFiberMulEquiv :
    (Over.mk s ⟶ (restrictedGroupScheme f s M).X) ≃* M := by
  letI := restrictedAction f s M
  letI := restrictedContinuousSMul f s M
  exact groupFiberMulEquiv s M

omit [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (s ≫ f))] in
/-- The restricted marking intertwines actual fibre-automorphism evaluation
with the restricted coefficient action in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem restrictedGroupFiber_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (restrictedGroupScheme f s M).X) :
    restrictedGroupFiberMulEquiv f s M
        (a.hom.app (restrictedGroupCover f s M) p) =
      (inducedGroupHom f s a) • restrictedGroupFiberMulEquiv f s M p := by
  let := restrictedAction f s M
  let := restrictedContinuousSMul f s M
  exact groupFiber_action s M a p

/-- Pullback followed by the original descent marking gives a
multiplicative marking of the actual pulled-back group scheme, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def pullbackGroupFiberMulEquiv :
    (Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X) ≃* M :=
  (pullbackFiberMulEquiv f s (groupScheme (s ≫ f) M)).symm.trans
    (groupFiberMulEquiv (s ≫ f) M)

/-- Comparison of the original and restricted multiplicative fibre
markings, for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def coefficientFiberMulEquiv :
    (Over.mk (s ≫ f) ⟶ (groupScheme (s ≫ f) M).X) ≃*
      (Over.mk s ⟶ (restrictedGroupScheme f s M).X) :=
  (groupFiberMulEquiv (s ≫ f) M).trans (restrictedGroupFiberMulEquiv f s M).symm

/-- The fibre comparison preserves the prescribed coefficient marking in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem coefficientFiberMulEquiv_marking
    (p : Over.mk (s ≫ f) ⟶ (groupScheme (s ≫ f) M).X) :
    restrictedGroupFiberMulEquiv f s M (coefficientFiberMulEquiv f s M p) =
      groupFiberMulEquiv (s ≫ f) M p :=
  (restrictedGroupFiberMulEquiv f s M).apply_symm_apply _

/-- The multiplicative fibre comparison is equivariant for the actual
restricted fibre-group action in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem coefficientFiberMulEquiv_equivariant (a : FiberAutGroup s)
    (p : Fiber (s ≫ f) (groupCover (s ≫ f) M)) :
    coefficientFiberMulEquiv f s M
        ((inducedGroupHom f s a).hom.app (groupCover (s ≫ f) M) p) =
      a.hom.app (restrictedGroupCover f s M) (coefficientFiberMulEquiv f s M p) := by
  apply (restrictedGroupFiberMulEquiv f s M).injective
  calc
    _ = groupFiberMulEquiv (s ≫ f) M
        ((inducedGroupHom f s a).hom.app (groupCover (s ≫ f) M) p) :=
      coefficientFiberMulEquiv_marking f s M _
    _ = (inducedGroupHom f s a) • groupFiberMulEquiv (s ≫ f) M p :=
      groupFiber_action (s ≫ f) M (inducedGroupHom f s a) p
    _ = (inducedGroupHom f s a) •
        restrictedGroupFiberMulEquiv f s M (coefficientFiberMulEquiv f s M p) :=
      congrArg (fun m => (inducedGroupHom f s a) • m)
        (coefficientFiberMulEquiv_marking f s M p).symm
    _ = _ := (restrictedGroupFiber_action f s M a (coefficientFiberMulEquiv f s M p)).symm

/-- The group fibre marking constructs an isomorphism of actual classified
actions after restriction, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def coefficientActionIso :
    (ContAction.res FintypeCat (inducedGroupHom f s)).obj
        ((classification (s ≫ f)).functor.obj (groupCover (s ≫ f) M)) ≅
      (classification s).functor.obj (restrictedGroupCover f s M) :=
  ObjectProperty.isoMk _ (Action.mkIso
    (FintypeCat.equivEquivIso (coefficientFiberMulEquiv f s M).toEquiv) (by
      intro a
      apply FintypeCat.hom_ext
      intro p
      exact coefficientFiberMulEquiv_equivariant f s M a p))

/-- The canonical classification naturality isomorphism followed by the
coefficient marking comparison, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def classifiedGroupBaseChangeIso :
    (classification s).functor.obj ((baseChange f).obj (groupCover (s ≫ f) M)) ≅
      (classification s).functor.obj (restrictedGroupCover f s M) :=
  (classificationBaseChangeIso f s).app (groupCover (s ≫ f) M) ≪≫
    coefficientActionIso f s M

/-- The classified group comparison evaluates by the canonical fibre
projection and the multiplicative coefficient markings, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem classifiedGroupBaseChangeIso_apply
    (p : Fiber s ((baseChange f).obj (groupCover (s ≫ f) M))) :
    (classifiedGroupBaseChangeIso f s M).hom.hom.hom p =
      coefficientFiberMulEquiv f s M
        ((fiberBaseChangeEquiv f s (groupCover (s ≫ f) M)).symm p) := by
  change coefficientFiberMulEquiv f s M
    (((classificationBaseChangeIso f s).hom.app (groupCover (s ≫ f) M)).hom.hom p) = _
  rw [classificationBaseChangeIso_hom_apply]

/-- Faithful classification lifts the canonical comparison to an actual
finite-etale cover isomorphism in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def groupCoverBaseChangeIso :
    (baseChange f).obj (groupCover (s ≫ f) M) ≅ restrictedGroupCover f s M :=
  (classification s).functor.preimageIso (classifiedGroupBaseChangeIso f s M)

/-- The lifted actual cover comparison has exactly the canonical point
formula in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupCoverBaseChangeIso_fiber
    (p : Fiber s ((baseChange f).obj (groupCover (s ≫ f) M))) :
    p ≫ (groupCoverBaseChangeIso f s M).hom.hom =
      coefficientFiberMulEquiv f s M
        ((fiberBaseChangeEquiv f s (groupCover (s ≫ f) M)).symm p) := by
  have h : (classification s).functor.map (groupCoverBaseChangeIso f s M).hom =
      (classifiedGroupBaseChangeIso f s M).hom :=
    (classification s).functor.map_preimage _
  have hp := ConcreteCategory.congr_hom (C := FintypeCat)
    (congrArg (fun (g : (classification s).functor.obj
        ((baseChange f).obj (groupCover (s ≫ f) M)) ⟶
        (classification s).functor.obj (restrictedGroupCover f s M)) => g.hom.hom) h) p
  change p ≫ (groupCoverBaseChangeIso f s M).hom.hom =
    (classifiedGroupBaseChangeIso f s M).hom.hom.hom p at hp
  exact hp.trans (classifiedGroupBaseChangeIso_apply f s M p)

/-- The underlying actual scheme isomorphism between pulled-back and
restricted descended coefficient groups in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def groupUnderlyingIso :
    ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X ≅
      (restrictedGroupScheme f s M).X :=
  (forget S).mapIso (groupCoverBaseChangeIso f s M)

/-- The underlying scheme comparison agrees with the multiplicative
pullback marking in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupUnderlyingIso_marking
    (p : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X) :
    restrictedGroupFiberMulEquiv f s M (p ≫ (groupUnderlyingIso f s M).hom) =
      pullbackGroupFiberMulEquiv f s M p := by
  change restrictedGroupFiberMulEquiv f s M
    (p ≫ (groupCoverBaseChangeIso f s M).hom.hom) = _
  exact (congrArg (restrictedGroupFiberMulEquiv f s M)
    (groupCoverBaseChangeIso_fiber f s M p)).trans
    (coefficientFiberMulEquiv_marking f s M
      ((fiberBaseChangeEquiv f s (groupCover (s ≫ f) M)).symm p))

/-- Unit preservation on actual scheme-valued fibre points in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupUnderlyingIso_point_one :
    (1 : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X) ≫
        (groupUnderlyingIso f s M).hom = 1 := by
  apply (restrictedGroupFiberMulEquiv f s M).injective
  rw [groupUnderlyingIso_marking, map_one, map_one]

/-- Multiplication preservation on actual scheme-valued fibre points in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupUnderlyingIso_point_mul
    (p q : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X) :
    (p * q) ≫ (groupUnderlyingIso f s M).hom =
      (p ≫ (groupUnderlyingIso f s M).hom) * (q ≫ (groupUnderlyingIso f s M).hom) := by
  apply (restrictedGroupFiberMulEquiv f s M).injective
  rw [groupUnderlyingIso_marking, map_mul, map_mul,
    groupUnderlyingIso_marking, groupUnderlyingIso_marking]

/-- Fibre faithfulness promotes pointwise equality to equality of actual
scheme maps, auxiliary to coefficient transport in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
private theorem cover_morphism_ext {Y Z : Scheme.FiniteEtale S} {g h : Y.obj ⟶ Z.obj}
    (heq : ∀ p : Fiber s Y, p ≫ g = p ≫ h) : g = h := by
  have hh : (fiberToFinite s).map (ObjectProperty.homMk g) =
      (fiberToFinite s).map (ObjectProperty.homMk h) :=
    FintypeCat.hom_ext _ _ heq
  exact congrArg (fun g => g.hom) ((fiberToFinite s).map_injective hh)

omit [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (s ≫ f))] in
/-- For actual finite-etale group schemes, fibre faithfulness upgrades
proved point-group unit and multiplication laws to a scheme-group homomorphism,
auxiliary to `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
private theorem pointwiseIsMonHom (A B : Grp (Over S))
    [IsFinite A.X.hom] [Etale A.X.hom] [IsFinite B.X.hom] [Etale B.X.hom]
    (g : A.X ⟶ B.X)
    (hone : (1 : Over.mk s ⟶ A.X) ≫ g = 1)
    (hmul : ∀ p q : Over.mk s ⟶ A.X, (p * q) ≫ g = (p ≫ g) * (q ≫ g)) :
    IsMonHom g := by
  let Y : Scheme.FiniteEtale S := ⟨A.X, ⟨inferInstance, inferInstance⟩⟩
  let Z : Scheme.FiniteEtale S := ⟨B.X, ⟨inferInstance, inferInstance⟩⟩
  constructor
  · apply cover_morphism_ext (s := s) (Y := 𝟙_ (Scheme.FiniteEtale S)) (Z := Z)
    intro p
    have hp : p = toUnit (Over.mk s) := toUnit_unique p _
    subst p
    exact (Category.assoc _ _ _).symm.trans hone
  · apply cover_morphism_ext (s := s) (Y := Y ⊗ Y) (Z := Z)
    intro p
    rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    exact hmul _ _

/-- The cover comparison preserves the actual scheme-group unit, proved
from multiplicative fibre markings and faithfulness in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupUnderlyingIso_one :
    η[((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X] ≫
        (groupUnderlyingIso f s M).hom = η[(restrictedGroupScheme f s M).X] := by
  apply cover_morphism_ext (s := s) (Y := 𝟙_ (Scheme.FiniteEtale S))
    (Z := restrictedGroupCover f s M)
  intro p
  have hp : p = toUnit (Over.mk s) := toUnit_unique p _
  subst p
  exact (Category.assoc _ _ _).symm.trans (groupUnderlyingIso_point_one f s M)

/-- The cover comparison preserves actual scheme multiplication, proved
from multiplicative fibre markings and faithfulness in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupUnderlyingIso_mul :
    μ[((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X] ≫
        (groupUnderlyingIso f s M).hom =
      ((groupUnderlyingIso f s M).hom ⊗ₘ (groupUnderlyingIso f s M).hom) ≫
        μ[(restrictedGroupScheme f s M).X] := by
  exact (pointwiseIsMonHom s ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M))
    (restrictedGroupScheme f s M) (groupUnderlyingIso f s M).hom
    (groupUnderlyingIso_point_one f s M) (groupUnderlyingIso_point_mul f s M)).mul_hom

/-- Actual coefficient group schemes commute with pullback and restriction
of the actual continuous fibre-group action, in the coefficient transport
subset of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Unit and multiplication preservation are proved rather than supplied. -/
def groupSchemeBaseChangeIso :
    (Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M) ≅ restrictedGroupScheme f s M :=
  Grp.mkIso (groupUnderlyingIso f s M)
    (groupUnderlyingIso_one f s M) (groupUnderlyingIso_mul f s M)

/-- The group scheme isomorphism uses the proved underlying cover map in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChangeIso_hom :
    (groupSchemeBaseChangeIso f s M).hom.hom.hom = (groupUnderlyingIso f s M).hom := rfl

/-- The actual group scheme pullback isomorphism preserves the prescribed
coefficient marking in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupSchemeBaseChangeIso_marking
    (p : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme (s ≫ f) M)).X) :
    restrictedGroupFiberMulEquiv f s M (p ≫ (groupSchemeBaseChangeIso f s M).hom.hom.hom) =
      groupFiberMulEquiv (s ≫ f) M
        ((fiberBaseChangeEquiv f s (groupCover (s ≫ f) M)).symm p) := by
  rw [groupSchemeBaseChangeIso_hom, groupUnderlyingIso_marking]
  rfl

section Modules

variable (R : Type v) [AddCommGroup R] [Finite R] [TopologicalSpace R] [DiscreteTopology R]
  [DistribMulAction (FiberAutGroup (s ≫ f)) R]
  [ContinuousSMul (FiberAutGroup (s ≫ f)) R]

/-- Restrict the additive coefficient action along the actual fibre-group
map in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[instance_reducible] def restrictedModuleAction : DistribMulAction (FiberAutGroup s) R :=
  DistribMulAction.compHom R (inducedGroupHom f s).toMonoidHom

omit [Finite R] [DiscreteTopology R]
  [GaloisCategory (Scheme.FiniteEtale S)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  [GaloisCategory (Scheme.FiniteEtale X)] [PreGaloisCategory.FiberFunctor
    (fiberToFinite (s ≫ f))] in
/-- Continuity of the restricted additive coefficient action in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem restrictedModuleContinuousSMul :
    letI := restrictedModuleAction f s R
    ContinuousSMul (FiberAutGroup s) R := by
  let := restrictedModuleAction f s R
  exact ⟨(continuous_smul (M := FiberAutGroup (s ≫ f)) (X := R)).comp
    (((inducedGroupHom f s).continuous_toFun.comp continuous_fst).prodMk continuous_snd)⟩

/-- The restricted additive coefficient scheme in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedModuleScheme : Grp (Over S) := by
  letI := restrictedModuleAction f s R
  letI := restrictedModuleContinuousSMul f s R
  exact moduleScheme s R

/-- The restricted additive scheme's actual multiplicative point marking
in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedModuleFiberMulEquiv :
    (Over.mk s ⟶ (restrictedModuleScheme f s R).X) ≃* Multiplicative R := by
  letI := restrictedModuleAction f s R
  letI := restrictedModuleContinuousSMul f s R
  exact moduleFiberMulEquiv s R

/-- Additive action written on the multiplicative synonym, auxiliary to the
module specialization of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
private instance multiplicativeModuleAction :
    MulDistribMulAction (FiberAutGroup (s ≫ f)) (Multiplicative R) where
  smul a r := Multiplicative.ofAdd (a • r.toAdd)
  one_smul r := one_smul _ r.toAdd
  mul_smul a b r := mul_smul a b r.toAdd
  smul_one a := congrArg Multiplicative.ofAdd (smul_zero a : a • (0 : R) = 0)
  smul_mul a r q := smul_add a r.toAdd q.toAdd

/-- Continuity on the multiplicative synonym, auxiliary to the module
specialization of `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
private instance multiplicativeModuleContinuous :
    ContinuousSMul (FiberAutGroup (s ≫ f)) (Multiplicative R) where
  continuous_smul := by
    change Continuous (fun p : FiberAutGroup (s ≫ f) × R => p.1 • p.2)
    exact continuous_smul

/-- The actual additive coefficient scheme commutes with scheme pullback
and restriction of the actual fibre-group action, in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def moduleSchemeBaseChangeIso :
    (Over.pullback f).mapGrp.obj (moduleScheme (s ≫ f) R) ≅ restrictedModuleScheme f s R :=
  groupSchemeBaseChangeIso f s (Multiplicative R)

/-- The module specialization preserves the same actual coefficient
marking as the general group theorem, in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem moduleSchemeBaseChangeIso_marking
    (p : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (moduleScheme (s ≫ f) R)).X) :
    restrictedModuleFiberMulEquiv f s R (p ≫ (moduleSchemeBaseChangeIso f s R).hom.hom.hom) =
      moduleFiberMulEquiv (s ≫ f) R
        ((fiberBaseChangeEquiv f s (groupCover (s ≫ f) (Multiplicative R))).symm p) :=
  groupSchemeBaseChangeIso_marking f s (Multiplicative R) p

end Modules

end AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange

/-!
The following equality-aware API extends the literal-composite-point API above.
For an independent target point `t` and `h : s ≫ f = t`, restriction uses the
actual `pointedMap (Under.homMk f h)`. This covers a rational-origin projection
whose composite-point equality is propositional. No equality of coefficient
actions or coefficient pullback isomorphism is supplied as an input.
The same module source identity and mathematical coverage boundary apply.
-/

namespace AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange

universe u v

attribute [local instance] Over.cartesianMonoidalCategory GroupDescent.coverCartesian

variable {S X : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
  (t : Spec (CommRingCat.of K) ⟶ X) (h : s ≫ f = t)

/-- The actual continuous pointed fibre-group map with an independent target
point in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def inducedGroupHomPointed : FiberAutGroup s →ₜ* FiberAutGroup t :=
  { pointedMap (Under.homMk f h : Under.mk s ⟶ Under.mk t) with
    continuous_toFun := continuous_pointedMap
      (Under.homMk f h : Under.mk s ⟶ Under.mk t) }

/-- The underlying map is exactly the actual pointed-scheme group map in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem inducedGroupHomPointed_toMonoidHom :
    (inducedGroupHomPointed f s t h).toMonoidHom =
      pointedMap (Under.homMk f h : Under.mk s ⟶ Under.mk t) := rfl

/-- In the literal-composite case the pointed map is the previously
constructed continuous group map in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem inducedGroupHomPointed_rfl :
    inducedGroupHomPointed f s (s ≫ f) rfl = inducedGroupHom f s := rfl

/-- The equality-aware continuous homomorphism normalizes exactly to the
actual projection group homomorphism in the rational-origin construction of
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem inducedGroupHomPointed_projection {B H : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : H ⟶ B) (o : B ⟶ H)
    (ho : o ≫ p = 𝟙 B) :
    (inducedGroupHomPointed p (b ≫ o) b (by simp [Category.assoc, ho])).toMonoidHom =
      projectionHom b p o ho := rfl

/-- The equality-aware map specializes to the actual arithmetic projection
for an `F`-scheme with rational origin in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem inducedGroupHomPointed_rationalPointProjection {F : Type u}
    [Field F] [Algebra F K] (H : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H) :
    (inducedGroupHomPointed H.hom (fieldPoint F K ≫ o.left) (fieldPoint F K)
      (by simp [Category.assoc, Over.w o])).toMonoidHom =
        rationalPointProjectionHom H o := rfl

/-- Canonical fibre transport for a point-preserving equality in the
coefficient pullback subset of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def fiberBaseChangeEquivPointed (Y : Scheme.FiniteEtale X) :
    Fiber t Y ≃ Fiber s ((baseChange f).obj Y) :=
  pointedFiberEquiv (Under.homMk f h : Under.mk s ⟶ Under.mk t) Y

/-- The equality-aware fibre transport recovers the actual literal-case
pullback equivalence in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem fiberBaseChangeEquivPointed_rfl (Y : Scheme.FiniteEtale X) :
    fiberBaseChangeEquivPointed f s (s ≫ f) rfl Y = fiberBaseChangeEquiv f s Y := by
  apply Equiv.ext
  intro p
  change (fiberToFiniteBaseChangeIso f s).hom.app Y p = fiberBaseChangeEquiv f s Y p
  exact finiteBaseChangeIso_hom_apply f s Y p

variable (M : Type v) [Group M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (FiberAutGroup t) M] [ContinuousSMul (FiberAutGroup t) M]

/-- Restriction along the actual pointed fibre-group homomorphism in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[instance_reducible] def restrictedActionPointed : MulDistribMulAction (FiberAutGroup s) M :=
  MulDistribMulAction.compHom M (inducedGroupHomPointed f s t h).toMonoidHom

omit [Finite M] [DiscreteTopology M] in
/-- Joint continuity of the actual pointed restriction in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem restrictedContinuousSMulPointed :
    letI := restrictedActionPointed f s t h M
    ContinuousSMul (FiberAutGroup s) M := by
  let := restrictedActionPointed f s t h M
  exact ⟨(continuous_smul (M := FiberAutGroup t) (X := M)).comp
    (((inducedGroupHomPointed f s t h).continuous_toFun.comp continuous_fst).prodMk
      continuous_snd)⟩

variable [GaloisCategory (Scheme.FiniteEtale S)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite t)]

/-- The actual group scheme descended at `s` with coefficient action
restricted along the specified pointed map, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedGroupSchemePointed : Grp (Over S) := by
  letI := restrictedActionPointed f s t h M
  letI := restrictedContinuousSMulPointed f s t h M
  exact groupScheme s M

/-- The actual multiplicative coefficient marking for pointed restriction
in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def restrictedGroupFiberMulEquivPointed :
    (Over.mk s ⟶ (restrictedGroupSchemePointed f s t h M).X) ≃* M := by
  letI := restrictedActionPointed f s t h M
  letI := restrictedContinuousSMulPointed f s t h M
  exact groupFiberMulEquiv s M

/-- Equality-aware coefficient pullback is an actual group scheme
isomorphism. Restriction uses the actual `pointedMap`, and the group laws
follow from the proved literal-case theorem, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def groupSchemeBaseChangeIsoPointed :
    (Over.pullback f).mapGrp.obj (groupScheme t M) ≅
      restrictedGroupSchemePointed f s t h M := by
  subst t
  exact groupSchemeBaseChangeIso f s M

/-- The underlying scheme comparison in the equality-aware coefficient
pullback theorem, for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def groupUnderlyingIsoPointed :
    ((Over.pullback f).mapGrp.obj (groupScheme t M)).X ≅
      (restrictedGroupSchemePointed f s t h M).X := by
  subst t
  exact groupUnderlyingIso f s M

/-- The equality-aware group isomorphism has exactly the canonical
underlying scheme homomorphism, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem groupSchemeBaseChangeIsoPointed_hom :
    (groupSchemeBaseChangeIsoPointed f s t h M).hom.hom.hom =
      (groupUnderlyingIsoPointed f s t h M).hom := by
  subst t
  exact groupSchemeBaseChangeIso_hom f s M

/-- The pointed group scheme comparison has the canonical fibre projection
and the same original coefficient marking, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem groupSchemeBaseChangeIsoPointed_marking
    (q : Over.mk s ⟶ ((Over.pullback f).mapGrp.obj (groupScheme t M)).X) :
    restrictedGroupFiberMulEquivPointed f s t h M
        (q ≫ (groupSchemeBaseChangeIsoPointed f s t h M).hom.hom.hom) =
      groupFiberMulEquiv t M
        ((fiberBaseChangeEquivPointed f s t h (groupCover t M)).symm q) := by
  subst t
  change restrictedGroupFiberMulEquiv f s M
      (q ≫ (groupSchemeBaseChangeIso f s M).hom.hom.hom) =
    groupFiberMulEquiv (s ≫ f) M
      ((fiberBaseChangeEquivPointed f s (s ≫ f) rfl (groupCover (s ≫ f) M)).symm q)
  rw [fiberBaseChangeEquivPointed_rfl]
  exact groupSchemeBaseChangeIso_marking f s M q

end AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8b019e73ade750263686d5f8ef33ffe865533b4190ac17e57b87bb6c8c25dfab.
Definitions, hypotheses and universes are retained modulo native names. -/
