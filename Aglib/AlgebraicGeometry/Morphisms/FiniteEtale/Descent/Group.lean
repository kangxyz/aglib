/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Topology.Instances.ZMod

/-!
# Finite group and module descent through the actual fibre functor

Source: `K2-018#prop:k2018-arithmetic-characters` and
`K2-018#eq:k2018-pointed-character`, lines 341–445 of
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, manuscript SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The corresponding consumer is `R5Lab.Galois.CharacterIsogenies`.

The scheme category, finite étale covers and finite-valued fibre functor are
actual existing objects. The accepted `FiniteEtaleCovers.lean` input has SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6`;
`EtaleFundamentalGroups.lean` has SHA256
`f45f9cb6815524a8b04347d98bd51d0a95dd787e6499cec65af8a8171c31101f`.

The retained standard theorem input is exactly
`[GaloisCategory (Cover B)]` and
`[PreGaloisCategory.FiberFunctor (fiberToFinite s)]`.
For `B = Spec F` and a geometric point these are the usual finite étale
scheme Galois-category and fibre-functor axioms. Their geometric verification
is not recreated here. Mathlib's `PreGaloisCategory.functorToContAction`,
`CategoryTheory/Galois/Equivalence.lean:33–90`, proves the resulting categorical
equivalence from these classes.

The specialized descent is constructed: a finite continuous group action is
an internal group in the continuous-action category, the inverse equivalence
transports it to `Cover B`, and the proved finite-product-compatible inclusion
transports it to `Grp (Over B)`. The counit supplies the fibre marking; its
multiplicativity and compatibility with the actual natural fibre-automorphism
action are proved. Mathlib's finite-type universe switch permits an arbitrary
coefficient universe without changing the public marking target.

`moduleScheme` applies this construction to an additive finite module, and
`selectedPointCyclic` identifies the selected fibre of `cyclicScheme` with
`Multiplicative (ZMod n)`. This does not prove the `CyclicCoefficient`
condition at every algebraically closed field-valued point. That change-of-point
bridge is separate, as is identification of a particular arithmetic or
cyclotomic action with this actual fibre-automorphism group.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite forget)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
universe u v

attribute [local instance] Over.cartesianMonoidalCategory

/-- Actual finite étale fibre products and the identity cover give the
Cartesian structure on `Cover B`, without Galois-category hypotheses. -/
abbrev coverCartesian (X : Scheme.{u}) : CartesianMonoidalCategory (Scheme.FiniteEtale X) where
  __ := MonoidalCategory.fullSubcategory (_root_.AlgebraicGeometry.Scheme.finiteEtaleProperty X)
    (by change IsFinite (𝟙 X) ∧ Etale (𝟙 X); exact ⟨inferInstance, inferInstance⟩)
    (fun Y Z hY hZ => by
      let : IsFinite Y.hom := hY.1
      let : Etale Y.hom := hY.2
      let : IsFinite Z.hom := hZ.1
      let : Etale Z.hom := hZ.2
      change IsFinite (pullback.fst Y.hom Z.hom ≫ Y.hom) ∧
        Etale (pullback.fst Y.hom Z.hom ≫ Y.hom)
      exact ⟨inferInstance, inferInstance⟩)
  isTerminalTensorUnit := .ofUniqueHom (fun Y => ObjectProperty.homMk (toUnit Y.obj))
    (fun _ _ => by apply ObjectProperty.hom_ext; apply toUnit_unique)
  fst Y Z := ObjectProperty.homMk (fst Y.obj Z.obj)
  snd Y Z := ObjectProperty.homMk (snd Y.obj Z.obj)
  tensorProductIsBinaryProduct Y Z :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def Y Z := by apply ObjectProperty.hom_ext; exact fst_def Y.obj Z.obj
  snd_def Y Z := by apply ObjectProperty.hom_ext; exact snd_def Y.obj Z.obj

attribute [local instance] coverCartesian

/-- The inclusion of actual finite étale covers preserves the chosen
terminal object and fibre products, hence transports internal group laws. -/
instance coverForgetMonoidal (X : Scheme.{u}) : (forget X).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

/-- Finite-product preservation of the actual inclusion into schemes over `B`. -/
theorem forget_preservesFiniteProducts (X : Scheme.{u}) :
    PreservesFiniteProducts (forget X) := inferInstance

/-- The Cartesian monoidal structure on finite types, with products and the singleton unit. -/
abbrev finiteCartesian : CartesianMonoidalCategory FintypeCat.{u} where
  __ := MonoidalCategory.fullSubcategory (C := Type u) Finite
    (by change Finite PUnit; infer_instance)
    (fun X Y hX hY => by let := hX; let := hY; change Finite (X × Y); infer_instance)
  isTerminalTensorUnit := .ofUniqueHom (fun _ => ObjectProperty.homMk (↾fun _ => PUnit.unit))
    (fun X f => by
      apply FintypeCat.hom_ext
      intro p
      change (f p : PUnit) = PUnit.unit
      exact @Subsingleton.elim PUnit inferInstance (f p) PUnit.unit)
  fst X Y := ObjectProperty.homMk (↾Prod.fst)
  snd X Y := ObjectProperty.homMk (↾Prod.snd)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (↾fun p => (f p, g p)))
      (by intros; apply FintypeCat.hom_ext; intro; rfl)
      (by intros; apply FintypeCat.hom_ext; intro; rfl)
      (by intro W f g h hfst hsnd; apply FintypeCat.hom_ext; intro p
          exact Prod.ext (ConcreteCategory.congr_hom hfst p)
            (ConcreteCategory.congr_hom hsnd p))
  fst_def X Y := by apply FintypeCat.hom_ext; intro; rfl
  snd_def X Y := by apply FintypeCat.hom_ext; intro; rfl

attribute [local instance] finiteCartesian

/-- The Cartesian monoidal structure on finite `G`-sets, with diagonal product actions. -/
abbrev actionCartesian (G : Type*) [Group G] :
    CartesianMonoidalCategory (Action FintypeCat.{u} G) where
  __ := Action.instMonoidalCategory
  isTerminalTensorUnit := .ofUniqueHom (fun X =>
      { hom := toUnit X.V
        comm g := by apply FintypeCat.hom_ext; intro; rfl })
    (fun _ _ => by apply Action.Hom.ext; apply toUnit_unique)
  fst X Y := { hom := fst X.V Y.V
               comm g := by apply FintypeCat.hom_ext; intro; rfl }
  snd X Y := { hom := snd X.V Y.V
               comm g := by apply FintypeCat.hom_ext; intro; rfl }
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g =>
      { hom := lift f.hom g.hom
        comm a := by
          apply FintypeCat.hom_ext; intro p
          exact Prod.ext (ConcreteCategory.congr_hom (f.comm a) p)
            (ConcreteCategory.congr_hom (g.comm a) p) })
      (by intros; apply Action.Hom.ext; apply FintypeCat.hom_ext; intro; rfl)
      (by intros; apply Action.Hom.ext; apply FintypeCat.hom_ext; intro; rfl)
      (by intro W f g h hfst hsnd; apply Action.Hom.ext; apply FintypeCat.hom_ext; intro p
          exact Prod.ext (ConcreteCategory.congr_hom (congrArg Action.Hom.hom hfst) p)
            (ConcreteCategory.congr_hom (congrArg Action.Hom.hom hsnd) p))
  fst_def X Y := by apply Action.Hom.ext; apply FintypeCat.hom_ext; intro; rfl
  snd_def X Y := by apply Action.Hom.ext; apply FintypeCat.hom_ext; intro; rfl

attribute [local instance] actionCartesian

instance continuousCartesian (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CartesianMonoidalCategory (ContAction FintypeCat.{u} G) :=
  CartesianMonoidalCategory.fullSubcategory

variable {B : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ B)

/-- The prescribed finite discrete group action as a continuous action object. -/
abbrev finiteGroupAction (M : Type u) [Group M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (FiberAutGroup s) M]
    [ContinuousSMul (FiberAutGroup s) M] : ContAction FintypeCat.{u} (FiberAutGroup s) :=
  ⟨{ V := FintypeCat.of M
     ρ := (Action.FintypeCat.ofMulAction (FiberAutGroup s) (FintypeCat.of M)).ρ }, by
    let h := (inferInstance : ContinuousSMul (FiberAutGroup s) M)
    rw [DiscreteTopology.eq_bot (α := M)] at h
    exact h⟩

instance finiteGroupActionGrp (M : Type u) [Group M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (FiberAutGroup s) M]
    [ContinuousSMul (FiberAutGroup s) M] : GrpObj (finiteGroupAction s M) where
  one := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun _ => (1 : M))
      comm a := by
        apply FintypeCat.hom_ext; intro p
        change (1 : M) = a • (1 : M)
        exact (smul_one a).symm }
  mul := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun p => (p.1 : M) * (p.2 : M))
      comm a := by
        apply FintypeCat.hom_ext; intro p
        exact ((MulDistribMulAction.toMonoidHom M a).map_mul p.1 p.2).symm }
  inv := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun p => (p : M)⁻¹)
      comm a := by
        apply FintypeCat.hom_ext; intro p
        exact ((MulDistribMulAction.toMonoidHom M a).map_inv p).symm }
  one_mul := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; apply FintypeCat.hom_ext
    intro p
    change (1 : M) * (p.2 : M) = p.2
    exact _root_.one_mul _
  mul_one := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; apply FintypeCat.hom_ext
    intro p
    change (p.1 : M) * 1 = p.1
    exact _root_.mul_one _
  mul_assoc := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; apply FintypeCat.hom_ext
    intro p
    change ((p.1.1 : M) * (p.1.2 : M)) * (p.2 : M) = _
    exact _root_.mul_assoc _ _ _
  left_inv := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; apply FintypeCat.hom_ext
    intro p
    change (p : M)⁻¹ * (p : M) = 1
    exact inv_mul_cancel _
  right_inv := by
    apply ObjectProperty.hom_ext; apply Action.Hom.ext; apply FintypeCat.hom_ext
    intro p
    change (p : M) * (p : M)⁻¹ = 1
    exact mul_inv_cancel _

/-- The group object of finite continuous fibre-group actions determined by the given action on
the finite discrete group `M`. -/
abbrev finiteActionGroup (M : Type u) [Group M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (FiberAutGroup s) M]
    [ContinuousSMul (FiberAutGroup s) M] : Grp (ContAction FintypeCat.{u} (FiberAutGroup s)) :=
  Grp.mk (finiteGroupAction s M)

section Classification

variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- The exact generic Galois-category equivalence applied to the actual
finite étale fibre functor. The two library classes above are retained inputs. -/
def classification : Scheme.FiniteEtale B ≌ ContAction FintypeCat.{u} (FiberAutGroup s) :=
  (PreGaloisCategory.functorToContAction (fiberToFinite s)).asEquivalence

instance classificationFunctorMonoidal : (classification s).functor.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

instance classificationInverseMonoidal : (classification s).inverse.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

variable (M : Type u) [Group M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]

/-- Descend the group law with the actual inverse equivalence. -/
def descendedGroup : Grp (Scheme.FiniteEtale B) :=
  (classification s).inverse.mapGrp.obj (finiteActionGroup s M)

/-- The marking is the group-object counit of the generic equivalence. -/
def descendedGroupMarking :
    (classification s).functor.mapGrp.obj (descendedGroup s M) ≅ finiteActionGroup s M :=
  (classification s).mapGrp.counitIso.app (finiteActionGroup s M)

/-- An actual finite étale group scheme over `B`, constructed from descent. -/
def coefficientScheme : Grp (Over B) :=
  (forget B).mapGrp.obj (descendedGroup s M)

instance coefficientScheme_finite : IsFinite (coefficientScheme s M).X.hom :=
  (descendedGroup s M).X.property.1

instance coefficientScheme_etale : Etale (coefficientScheme s M).X.hom :=
  (descendedGroup s M).X.property.2

/-- The identification of the coefficient scheme fibre with `M` supplied by the descended group
marking. -/
def fiberEquiv : (Over.mk s ⟶ (coefficientScheme s M).X) ≃ M :=
  FintypeCat.equivEquivIso.symm
    { hom := (descendedGroupMarking s M).hom.hom.hom.hom.hom
      inv := (descendedGroupMarking s M).inv.hom.hom.hom.hom
      hom_inv_id := by
        exact congrArg (fun f => f.hom.hom.hom.hom)
          (descendedGroupMarking s M).hom_inv_id
      inv_hom_id := by
        exact congrArg (fun f => f.hom.hom.hom.hom)
          (descendedGroupMarking s M).inv_hom_id }

theorem fiberEquiv_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (coefficientScheme s M).X) :
    fiberEquiv s M (a.hom.app (descendedGroup s M).X p) = a • fiberEquiv s M p := by
  exact ConcreteCategory.congr_hom
    ((descendedGroupMarking s M).hom.hom.hom.hom.comm a) p

/-- On the actual geometric fibre, the monoidal product comparison is
precisely the universal fibre-product lift of the two scheme-valued points. -/
private theorem classificationProduct (Y Z : Scheme.FiniteEtale B) (p : Fiber s Y) (q : Fiber s Z) :
    (Functor.LaxMonoidal.μ (classification s).functor Y Z).hom.hom (p, q) = lift p q := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := ConcreteCategory.congr_hom (C := FintypeCat)
      (congrArg (fun f => f.hom.hom)
        (Functor.Monoidal.μ_fst (classification s).functor Y Z)) (p, q)
    change (Functor.LaxMonoidal.μ (classification s).functor Y Z).hom.hom (p, q) ≫
      (fst Y Z).hom = p at h
    have hf : (fst Y Z).hom.left = pullback.fst Y.obj.hom Z.obj.hom := rfl
    simpa only [Over.comp_left, Over.lift_left, pullback.lift_fst, hf] using
      congrArg Over.Hom.left h
  · have h := ConcreteCategory.congr_hom (C := FintypeCat)
      (congrArg (fun f => f.hom.hom)
        (Functor.Monoidal.μ_snd (classification s).functor Y Z)) (p, q)
    change (Functor.LaxMonoidal.μ (classification s).functor Y Z).hom.hom (p, q) ≫
      (snd Y Z).hom = q at h
    have hs : (snd Y Z).hom.left = pullback.snd Y.obj.hom Z.obj.hom := rfl
    simpa only [Over.comp_left, Over.lift_left, pullback.lift_snd, hs] using
      congrArg Over.Hom.left h

@[simp] theorem coefficientScheme_mul :
    μ[(coefficientScheme s M).X] = (μ[(descendedGroup s M).X]).hom := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

theorem fiberEquiv_mul (p q : Over.mk s ⟶ (coefficientScheme s M).X) :
    fiberEquiv s M (p * q) = fiberEquiv s M p * fiberEquiv s M q := by
  have h := ConcreteCategory.congr_hom (C := FintypeCat)
    (congrArg (fun f => f.hom.hom)
      (IsMonHom.mul_hom (descendedGroupMarking s M).hom.hom.hom)) (p, q)
  change fiberEquiv s M
    ((Functor.LaxMonoidal.μ (classification s).functor
      (descendedGroup s M).X (descendedGroup s M).X).hom.hom (p, q) ≫
      (μ[(descendedGroup s M).X]).hom) = _ at h
  rw [classificationProduct] at h
  change fiberEquiv s M (lift p q ≫ μ[(coefficientScheme s M).X]) = _
  rw [coefficientScheme_mul]
  exact h

/-- The counit marking preserves the actual group law on scheme-valued points. -/
def fiberMulEquiv : (Over.mk s ⟶ (coefficientScheme s M).X) ≃* M :=
  { fiberEquiv s M with map_mul' := fiberEquiv_mul s M }

theorem fiberMulEquiv_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (coefficientScheme s M).X) :
    fiberMulEquiv s M (a.hom.app (descendedGroup s M).X p) =
      a • fiberMulEquiv s M p :=
  fiberEquiv_action s M a p

end Classification

section UniverseChange

instance switchedGroup (M : Type v) [Group M] [Finite M] :
    Group (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M)) :=
  (FintypeCat.uSwitchEquiv.{v, u} (FintypeCat.of M)).group

/-- The multiplicative equivalence from the universe-switched finite group back to `M`. -/
def switchedMulEquiv (M : Type v) [Group M] [Finite M] :
    FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M) ≃* M :=
  (FintypeCat.uSwitchEquiv.{v, u} (FintypeCat.of M)).mulEquiv

instance switchedAction {G : Type*} [Monoid G]
    (M : Type v) [Group M] [Finite M] [MulDistribMulAction G M] :
    MulDistribMulAction G (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M)) where
  smul a r := (switchedMulEquiv.{u, v} M).symm (a • switchedMulEquiv.{u, v} M r)
  one_smul r := by
    apply (switchedMulEquiv.{u, v} M).injective
    change (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
      (1 • switchedMulEquiv.{u, v} M r)) = _
    simp only [MulEquiv.apply_symm_apply, one_smul]
  mul_smul a b r := by
    apply (switchedMulEquiv.{u, v} M).injective
    change (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
      ((a * b) • switchedMulEquiv.{u, v} M r)) =
      (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
        (a • (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
          (b • switchedMulEquiv.{u, v} M r))))
    simp only [MulEquiv.apply_symm_apply, mul_smul]
  smul_one a := by
    apply (switchedMulEquiv.{u, v} M).injective
    change (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
      (a • switchedMulEquiv.{u, v} M 1)) = _
    simp only [map_one, smul_one]
  smul_mul a r t := by
    apply (switchedMulEquiv.{u, v} M).injective
    change (switchedMulEquiv.{u, v} M) ((switchedMulEquiv.{u, v} M).symm
      (a • switchedMulEquiv.{u, v} M (r * t))) =
      (switchedMulEquiv.{u, v} M) (((switchedMulEquiv.{u, v} M).symm
        (a • switchedMulEquiv.{u, v} M r)) * ((switchedMulEquiv.{u, v} M).symm
          (a • switchedMulEquiv.{u, v} M t)))
    simp only [MulEquiv.apply_symm_apply, map_mul, smul_mul']

instance switchedContinuous {G : Type*} [Monoid G] [TopologicalSpace G]
    (M : Type v) [Group M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction G M] [ContinuousSMul G M] :
    ContinuousSMul G (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M)) where
  continuous_smul :=
    (continuous_of_discreteTopology : Continuous (switchedMulEquiv.{u, v} M).symm).comp
      (continuous_smul.comp (continuous_fst.prodMk
        ((continuous_of_discreteTopology : Continuous (switchedMulEquiv.{u, v} M)).comp
          continuous_snd)))

variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable (M : Type v) [Group M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]

/-- The actual descended finite étale cover for a coefficient in any universe. -/
def groupCover : Scheme.FiniteEtale B :=
  (descendedGroup s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))).X

/-- An actual finite étale group scheme for an arbitrary finite continuous
coefficient group; the universe switch uses a proved equivalence of finite types. -/
def groupScheme : Grp (Over B) :=
  coefficientScheme s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))

instance groupScheme_finite : IsFinite (groupScheme s M).X.hom :=
  coefficientScheme_finite s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))

instance groupScheme_etale : Etale (groupScheme s M).X.hom :=
  coefficientScheme_etale s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))

/-- The actual point-valued fibre is the original prescribed group,
with its multiplication, in the original coefficient universe. -/
def groupFiberMulEquiv : (Over.mk s ⟶ (groupScheme s M).X) ≃* M :=
  (fiberMulEquiv s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))).trans
    (switchedMulEquiv.{u, v} M)

/-- The marking intertwines natural fibre-automorphism evaluation with the
prescribed coefficient action. -/
theorem groupFiber_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (groupScheme s M).X) :
    groupFiberMulEquiv s M (a.hom.app (groupCover s M) p) = a • groupFiberMulEquiv s M p := by
  change switchedMulEquiv.{u, v} M
    (fiberMulEquiv s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M))
      (a.hom.app (groupCover s M) p)) = a • switchedMulEquiv.{u, v} M
        (fiberMulEquiv s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M)) p)
  have h := fiberMulEquiv_action s (FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of M)) a p
  exact (congrArg (switchedMulEquiv.{u, v} M) h).trans
    ((switchedMulEquiv.{u, v} M).apply_symm_apply _)

/-- Natural evaluation is an action by group automorphisms on actual
scheme-valued points; distributivity follows from the proved marking. -/
abbrev groupFiberAction :
    MulDistribMulAction (FiberAutGroup s) (Over.mk s ⟶ (groupScheme s M).X) where
  smul a p := a.hom.app (groupCover s M) p
  one_smul p := rfl
  mul_smul a b p := rfl
  smul_one a := by
    apply (groupFiberMulEquiv s M).injective
    exact (groupFiber_action s M a 1).trans (by simp)
  smul_mul a p q := by
    apply (groupFiberMulEquiv s M).injective
    let ap : Over.mk s ⟶ (groupScheme s M).X := a.hom.app (groupCover s M) p
    let aq : Over.mk s ⟶ (groupScheme s M).X := a.hom.app (groupCover s M) q
    change groupFiberMulEquiv s M (a.hom.app (groupCover s M) (p * q)) =
      groupFiberMulEquiv s M (ap * aq)
    calc
      groupFiberMulEquiv s M (a.hom.app (groupCover s M) (p * q)) =
          a • groupFiberMulEquiv s M (p * q) := groupFiber_action s M a (p * q)
      _ = (a • groupFiberMulEquiv s M p) * (a • groupFiberMulEquiv s M q) := by
        rw [map_mul, smul_mul']
      _ = groupFiberMulEquiv s M ap * groupFiberMulEquiv s M aq := by
        dsimp only [ap, aq]
        rw [groupFiber_action, groupFiber_action]
      _ = groupFiberMulEquiv s M (ap * aq) := (groupFiberMulEquiv s M).map_mul ap aq |>.symm

end UniverseChange

section Modules

instance moduleMultiplicativeAction {G R : Type*} [Monoid G] [AddCommGroup R]
    [DistribMulAction G R] : MulDistribMulAction G (Multiplicative R) where
  smul a r := Multiplicative.ofAdd (a • r.toAdd)
  one_smul r := by exact one_smul G r.toAdd
  mul_smul a b r := by exact mul_smul a b r.toAdd
  smul_one a := by
    change Multiplicative.ofAdd (a • (0 : R)) = Multiplicative.ofAdd (0 : R)
    exact congrArg Multiplicative.ofAdd (smul_zero a : a • (0 : R) = 0)
  smul_mul a r t := by exact smul_add a r.toAdd t.toAdd

instance moduleMultiplicativeContinuous {G R : Type*} [Monoid G]
    [TopologicalSpace G] [AddCommGroup R] [TopologicalSpace R] [DistribMulAction G R]
    [ContinuousSMul G R] : ContinuousSMul G (Multiplicative R) where
  continuous_smul := by
    change Continuous (fun p : G × R => p.1 • p.2)
    exact continuous_smul

variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable (R : Type v) [AddCommGroup R] [Finite R] [TopologicalSpace R] [DiscreteTopology R]
  [DistribMulAction (FiberAutGroup s) R] [ContinuousSMul (FiberAutGroup s) R]

/-- Descend a finite additive module to an actual finite étale group scheme. -/
def moduleScheme : Grp (Over B) := groupScheme s (Multiplicative R)

instance moduleScheme_finite : IsFinite (moduleScheme s R).X.hom :=
  groupScheme_finite s (Multiplicative R)

instance moduleScheme_etale : Etale (moduleScheme s R).X.hom :=
  groupScheme_etale s (Multiplicative R)

/-- The geometric marking has exactly the original `Multiplicative R` target. -/
def moduleFiberMulEquiv : (Over.mk s ⟶ (moduleScheme s R).X) ≃* Multiplicative R :=
  groupFiberMulEquiv s (Multiplicative R)

/-- The multiplicative fibre-group action on the fibre of the descended module scheme. -/
abbrev moduleFiberAction :
    MulDistribMulAction (FiberAutGroup s) (Over.mk s ⟶ (moduleScheme s R).X) :=
  groupFiberAction s (Multiplicative R)

/-- The actual fibre action becomes the prescribed additive module action. -/
theorem moduleFiber_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (moduleScheme s R).X) :
    moduleFiberMulEquiv s R (a.hom.app (groupCover s (Multiplicative R)) p) =
      Multiplicative.ofAdd (a • (moduleFiberMulEquiv s R p).toAdd) :=
  groupFiber_action s (Multiplicative R) a p

end Modules

section Cyclic

variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
variable (n : ℕ) [NeZero n] [DistribMulAction (FiberAutGroup s) (ZMod n)]
  [ContinuousSMul (FiberAutGroup s) (ZMod n)]

/-- The actual coefficient scheme for the supplied continuous action on
`ZMod n`. Full closed-field invariance is not assumed in this constructor. -/
def cyclicScheme : Grp (Over B) := moduleScheme s (ZMod n)

instance cyclicScheme_finite : IsFinite (cyclicScheme s n).X.hom :=
  moduleScheme_finite s (ZMod n)

instance cyclicScheme_etale : Etale (cyclicScheme s n).X.hom :=
  moduleScheme_etale s (ZMod n)

/-- Cyclicity at the selected field-valued point. This supplies only the
selected-point clause, not the all-closed-field `CyclicCoefficient` bridge. -/
def selectedPointCyclic : (Over.mk s ⟶ (cyclicScheme s n).X) ≃* Multiplicative (ZMod n) :=
  moduleFiberMulEquiv s (ZMod n)

/-- The multiplicative fibre-group action on the fibre of the descended cyclic coefficient
scheme. -/
abbrev cyclicFiberAction :
    MulDistribMulAction (FiberAutGroup s) (Over.mk s ⟶ (cyclicScheme s n).X) :=
  moduleFiberAction s (ZMod n)

theorem selectedPointCyclic_action (a : FiberAutGroup s)
    (p : Over.mk s ⟶ (cyclicScheme s n).X) :
    selectedPointCyclic s n (a.hom.app (groupCover s (Multiplicative (ZMod n))) p) =
      Multiplicative.ofAdd (a • (selectedPointCyclic s n p).toAdd) :=
  moduleFiber_action s (ZMod n) a p

end Cyclic

end AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5ea2e4d2d770a3321b9747c1ffe3ba4b653632f650eb23826f2886ed82b98712.
Definitions, hypotheses and universes are retained modulo native names. -/
