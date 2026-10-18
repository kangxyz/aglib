/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Group
public import Aglib.CategoryTheory.TorsorAction.Basic

/-!
# Descent of finite continuous torsor actions to actual schemes

Source: `K2-018#prop:k2018-arithmetic-characters` and
`K2-018#eq:k2018-pointed-character`, `research/exposes/K2/018/expose.tex`
lines 341–445 at `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The actual consumer is `MarkedCovers.TorsorAction`; the finite monodromy
consumer is `R5Lab.Galois.CharacterIsogenies`.

The frozen `FiniteEtale/GroupDescent.lean` input has SHA256
`7d198fddef147ce2e7d8b8bf030e8bac7b3a698fa46f9c50b2a3b0308bbeecaf`.
The existing `MarkedCovers.lean` consumer has SHA256
`9900b7ad06e4a6c9b2bdff52b9bbb0893aa16d8c4f4abb311d0996c2e9eb80a0`.
The group-descent `Cover B`, `fiberToFinite s`, classification equivalence and
`groupScheme s R` are used unchanged.
The retained standard classification input is exactly
`[GaloisCategory (Cover B)]` and
`[PreGaloisCategory.FiberFunctor (fiberToFinite s)]`.

The additional inputs are ordinary finite continuous actions of
`Aut (fiberToFinite s)` on a group `R` and a set `T`, a genuine `MulAction R T`,
the twisting compatibility, and unique finite-set transport between existing
points. No scheme action, scheme transport, or transporter isomorphism is an
input. The finite transporter is proved bijective, the actual fibre functor
reflects its isomorphism, and inclusion carries this to a scheme isomorphism.
The scheme action laws follow from faithful descent of the finite action laws.

`schemeTransport_unique` and `schemeTorsorAction` quantify over every object
of `Over B`, including nonreduced schemes. They assert unique transport
between two already supplied points. They do not assert rational point lifts.
Nonemptiness of `T`, when supplied, is carried to the selected fibre by the
marking; local nonemptiness is separate from the `TorsorAction` interface.

This closes the finite-action-to-scheme-action layer. Geometric connectedness,
a rational origin, the comparison with sheaf H¹, and comparison with a group
pulled back from another base are separate. Here `R` and `T` share the universe
of the actual fibre functor; descent of arbitrary-universe torsor sets requires
an additional finite-type universe-switch interface.
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
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.TorsorDescent
universe u

attribute [local instance] Over.cartesianMonoidalCategory GroupDescent.coverCartesian

variable {B : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ B)
variable [GaloisCategory (Scheme.FiniteEtale B)] [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

variable (T : Type u) [Finite T] [TopologicalSpace T] [DiscreteTopology T]
  [MulAction (FiberAutGroup s) T] [ContinuousSMul (FiberAutGroup s) T]

/-- The prescribed continuous finite action as an actual classification object. -/
abbrev finiteSetAction : ContAction FintypeCat.{u} (FiberAutGroup s) :=
  ⟨{ V := FintypeCat.of T
     ρ := (Action.FintypeCat.ofMulAction (FiberAutGroup s) (FintypeCat.of T)).ρ }, by
    let h := (inferInstance : ContinuousSMul (FiberAutGroup s) T)
    rw [DiscreteTopology.eq_bot (α := T)] at h
    exact h⟩

/-- Descend the finite set with the inverse of the same actual classification. -/
def torsorCover : Scheme.FiniteEtale B := (classification s).inverse.obj (finiteSetAction s T)

/-- The counit identifies the selected point-valued fibre with the original set. -/
def torsorFiberEquiv : Fiber s (torsorCover s T) ≃ T :=
  FintypeCat.equivEquivIso.symm
    { hom := ((classification s).counitIso.app (finiteSetAction s T)).hom.hom.hom
      inv := ((classification s).counitIso.app (finiteSetAction s T)).inv.hom.hom
      hom_inv_id := congrArg (fun f => f.hom.hom)
        ((classification s).counitIso.app (finiteSetAction s T)).hom_inv_id
      inv_hom_id := congrArg (fun f => f.hom.hom)
        ((classification s).counitIso.app (finiteSetAction s T)).inv_hom_id }

/-- The set marking respects the natural fibre-automorphism action. -/
theorem torsorFiber_action (a : FiberAutGroup s) (p : Fiber s (torsorCover s T)) :
    torsorFiberEquiv s T (a.hom.app (torsorCover s T) p) = a • torsorFiberEquiv s T p :=
  ConcreteCategory.congr_hom (C := FintypeCat)
    (((classification s).counitIso.app (finiteSetAction s T)).hom.hom.comm a) p

omit [GaloisCategory (Scheme.FiniteEtale B)] in
@[simp] private theorem cover_fst (Y Z : Scheme.FiniteEtale B) : (fst Y Z).hom = fst Y.obj Z.obj
  := rfl

omit [GaloisCategory (Scheme.FiniteEtale B)] in
@[simp] private theorem cover_snd (Y Z : Scheme.FiniteEtale B) : (snd Y Z).hom = snd Y.obj Z.obj
  := rfl

omit [GaloisCategory (Scheme.FiniteEtale B)] in
@[simp] private theorem cover_lift {X Y Z : Scheme.FiniteEtale B} (f : X ⟶ Y) (g : X ⟶ Z) :
    (lift f g).hom = lift f.hom g.hom := rfl

private def fiberProductEquiv (Y Z : Scheme.FiniteEtale B) :
    Fiber s (Y ⊗ Z) ≃ Fiber s Y × Fiber s Z where
  toFun p := (p ≫ (fst Y Z).hom, p ≫ (snd Y Z).hom)
  invFun p := lift p.1 p.2
  left_inv p := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  right_inv p := by
    apply Prod.ext <;> simp

variable (R : Type u) [Group R] [Finite R] [TopologicalSpace R] [DiscreteTopology R]
  [MulDistribMulAction (FiberAutGroup s) R] [ContinuousSMul (FiberAutGroup s) R]
  [MulAction R T]

variable (compatibility : ∀ (a : FiberAutGroup s) (r : R) (t : T),
  a • (r • t) = (a • r) • (a • t))

/-- Twisting compatibility makes the prescribed action a morphism of the
actual continuous-action category. -/
def finiteActionMap :
    (classification s).functor.obj (groupCover s R ⊗ torsorCover s T) ⟶
      (classification s).functor.obj (torsorCover s T) :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun q => (torsorFiberEquiv s T).symm
        (groupFiberMulEquiv s R (q ≫ (fst (groupCover s R) (torsorCover s T)).hom) •
          torsorFiberEquiv s T (q ≫ (snd (groupCover s R) (torsorCover s T)).hom)))
      comm a := by
        apply FintypeCat.hom_ext
        intro q
        apply (torsorFiberEquiv s T).injective
        have hf := evaluate_naturality s a (fst (groupCover s R) (torsorCover s T)) q
        have hs := evaluate_naturality s a (snd (groupCover s R) (torsorCover s T)) q
        change (a.hom.app _ q) ≫ (fst (groupCover s R) (torsorCover s T)).hom = _ at hf
        change (a.hom.app _ q) ≫ (snd (groupCover s R) (torsorCover s T)).hom = _ at hs
        change torsorFiberEquiv s T ((torsorFiberEquiv s T).symm
          (groupFiberMulEquiv s R ((a.hom.app _ q) ≫
            (fst (groupCover s R) (torsorCover s T)).hom) •
            torsorFiberEquiv s T ((a.hom.app _ q) ≫
              (snd (groupCover s R) (torsorCover s T)).hom))) =
          torsorFiberEquiv s T (a.hom.app (torsorCover s T) ((torsorFiberEquiv s T).symm
            (groupFiberMulEquiv s R (q ≫ (fst (groupCover s R) (torsorCover s T)).hom) •
              torsorFiberEquiv s T (q ≫ (snd (groupCover s R) (torsorCover s T)).hom))))
        rw [Equiv.apply_symm_apply, torsorFiber_action, Equiv.apply_symm_apply, hf, hs,
          groupFiber_action, torsorFiber_action]
        exact (compatibility a _ _).symm }

/-- Full faithfulness descends the finite action morphism to actual covers. -/
def coverActionMap : groupCover s R ⊗ torsorCover s T ⟶ torsorCover s T :=
  (classification s).functor.preimage (finiteActionMap s T R compatibility)

/-- The actual action morphism of schemes over `B`. -/
def schemeActionMap : (groupScheme s R).X ⊗ (torsorCover s T).obj ⟶ (torsorCover s T).obj :=
  (coverActionMap s T R compatibility).hom

/-- Evaluation of the descended action gives precisely the original finite action. -/
theorem schemeActionMap_fiber (q : Fiber s (groupCover s R ⊗ torsorCover s T)) :
    torsorFiberEquiv s T (q ≫ schemeActionMap s T R compatibility) =
      groupFiberMulEquiv s R (q ≫ (fst (groupCover s R) (torsorCover s T)).hom) •
        torsorFiberEquiv s T (q ≫ (snd (groupCover s R) (torsorCover s T)).hom) := by
  have h := ConcreteCategory.congr_hom (C := FintypeCat)
    (congrArg (fun f => f.hom.hom)
      ((classification s).functor.map_preimage (finiteActionMap s T R compatibility))) q
  change q ≫ schemeActionMap s T R compatibility = (torsorFiberEquiv s T).symm _ at h
  exact (congrArg (torsorFiberEquiv s T) h).trans ((torsorFiberEquiv s T).apply_symm_apply _)

theorem schemeActionMap_point (a : Over.mk s ⟶ (groupScheme s R).X)
    (x : Fiber s (torsorCover s T)) :
    torsorFiberEquiv s T (lift a x ≫ schemeActionMap s T R compatibility) =
      groupFiberMulEquiv s R a • torsorFiberEquiv s T x := by
  have h := schemeActionMap_fiber s T R compatibility (lift a x)
  change torsorFiberEquiv s T (lift a x ≫ schemeActionMap s T R compatibility) =
    groupFiberMulEquiv s R (lift a x ≫ fst (groupScheme s R).X (torsorCover s T).obj) •
      torsorFiberEquiv s T (lift a x ≫ snd (groupScheme s R).X (torsorCover s T).obj) at h
  simpa only [lift_fst, lift_snd] using h

private theorem cover_morphism_ext {Y Z : Scheme.FiniteEtale B} {f g : Y.obj ⟶ Z.obj}
    (h : ∀ p : Fiber s Y, p ≫ f = p ≫ g) : f = g := by
  have hh : (fiberToFinite s).map (ObjectProperty.homMk f) =
      (fiberToFinite s).map (ObjectProperty.homMk g) :=
    FintypeCat.hom_ext _ _ h
  exact congrArg (fun f => f.hom) ((fiberToFinite s).map_injective hh)

/-- The unit action law is an equality of actual scheme morphisms. -/
theorem schemeActionMap_one :
    lift (toUnit (torsorCover s T).obj ≫ η[(groupScheme s R).X])
      (𝟙 (torsorCover s T).obj) ≫ schemeActionMap s T R compatibility =
      𝟙 (torsorCover s T).obj := by
  apply cover_morphism_ext (s := s) (Y := torsorCover s T) (Z := torsorCover s T)
  intro p
  apply (torsorFiberEquiv s T).injective
  have h := schemeActionMap_point s T R compatibility
    (1 : Over.mk s ⟶ (groupScheme s R).X) p
  simp only [map_one, one_smul] at h
  simpa only [comp_lift_assoc, Category.assoc, Category.comp_id, comp_toUnit_assoc,
    Hom.one_def] using h

/-- The multiplication action law is an equality of actual scheme morphisms. -/
theorem schemeActionMap_mul :
    lift (fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
        μ[(groupScheme s R).X])
      (snd ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj) ≫
        schemeActionMap s T R compatibility =
    lift (fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
        fst (groupScheme s R).X (groupScheme s R).X)
      (lift (fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
          snd (groupScheme s R).X (groupScheme s R).X)
        (snd ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj) ≫
          schemeActionMap s T R compatibility) ≫ schemeActionMap s T R compatibility := by
  apply cover_morphism_ext (s := s)
    (Y := (groupCover s R ⊗ groupCover s R) ⊗ torsorCover s T) (Z := torsorCover s T)
  intro p
  apply (torsorFiberEquiv s T).injective
  simp only [comp_lift_assoc]
  rw [schemeActionMap_point, schemeActionMap_point, schemeActionMap_point]
  have hm : p ≫ fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
      μ[(groupScheme s R).X] =
      (p ≫ fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
        fst (groupScheme s R).X (groupScheme s R).X) *
      (p ≫ fst ((groupScheme s R).X ⊗ (groupScheme s R).X) (torsorCover s T).obj ≫
        snd (groupScheme s R).X (groupScheme s R).X) := by
    rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [Category.assoc]
  rw [hm, map_mul, mul_smul]

/-- The transporter sends `(r, t)` to `(r • t, t)`. -/
def coverTransporter : groupCover s R ⊗ torsorCover s T ⟶ torsorCover s T ⊗ torsorCover s T :=
  lift (coverActionMap s T R compatibility) (snd (groupCover s R) (torsorCover s T))

private def domainEquiv : Fiber s (groupCover s R ⊗ torsorCover s T) ≃ R × T :=
  (fiberProductEquiv s (groupCover s R) (torsorCover s T)).trans
    ((groupFiberMulEquiv s R).toEquiv.prodCongr (torsorFiberEquiv s T))

private def codomainEquiv : Fiber s (torsorCover s T ⊗ torsorCover s T) ≃ T × T :=
  (fiberProductEquiv s (torsorCover s T) (torsorCover s T)).trans
    ((torsorFiberEquiv s T).prodCongr (torsorFiberEquiv s T))

private theorem coverTransporter_fiber (p : Fiber s (groupCover s R ⊗ torsorCover s T)) :
    codomainEquiv s T ((fiberToFinite s).map (coverTransporter s T R compatibility) p) =
      ((domainEquiv s T R p).1 • (domainEquiv s T R p).2, (domainEquiv s T R p).2) := by
  apply Prod.ext
  · change torsorFiberEquiv s T
      ((p ≫ (coverTransporter s T R compatibility).hom) ≫
        (fst (torsorCover s T) (torsorCover s T)).hom) =
      groupFiberMulEquiv s R (p ≫ (fst (groupCover s R) (torsorCover s T)).hom) •
        torsorFiberEquiv s T (p ≫ (snd (groupCover s R) (torsorCover s T)).hom)
    simp only [coverTransporter, cover_lift, cover_fst, Category.assoc, lift_fst]
    exact schemeActionMap_fiber s T R compatibility p
  · change torsorFiberEquiv s T
      ((p ≫ (coverTransporter s T R compatibility).hom) ≫
        (snd (torsorCover s T) (torsorCover s T)).hom) =
      torsorFiberEquiv s T (p ≫ (snd (groupCover s R) (torsorCover s T)).hom)
    simp only [coverTransporter, cover_lift, cover_snd, Category.assoc, lift_snd]

variable (transport : ∀ (x y : T), ∃! r : R, r • x = y)

omit [Finite T] [TopologicalSpace T] [DiscreteTopology T]
  [Finite R] [TopologicalSpace R] [DiscreteTopology R] in
private theorem finiteTransporter_bijective
    (transport : ∀ (x y : T), ∃! r : R, r • x = y) :
    Function.Bijective (fun p : R × T => (p.1 • p.2, p.2)) := by
  constructor
  · rintro ⟨r, x⟩ ⟨r', x'⟩ h
    have hx := congrArg Prod.snd h
    change x = x' at hx
    subst x'
    obtain ⟨a, ha, hu⟩ := transport x (r • x)
    apply Prod.ext
    · exact (hu r rfl).trans (hu r' (congrArg Prod.fst h).symm).symm
    · rfl
  · rintro ⟨y, x⟩
    obtain ⟨r, hr, _⟩ := transport x y
    exact ⟨(r, x), Prod.ext hr rfl⟩

include transport in
/-- Unique finite-set transport proves bijectivity of the actual transporter fibre. -/
theorem coverTransporter_bijective :
    Function.Bijective ((fiberToFinite s).map (coverTransporter s T R compatibility)) := by
  constructor
  · intro p q h
    have hh := congrArg (codomainEquiv s T) h
    rw [coverTransporter_fiber, coverTransporter_fiber] at hh
    exact (domainEquiv s T R).injective ((finiteTransporter_bijective T R transport).1 hh)
  · intro q
    obtain ⟨p, hp⟩ := (finiteTransporter_bijective T R transport).2 (codomainEquiv s T q)
    refine ⟨(domainEquiv s T R).symm p, (codomainEquiv s T).injective ?_⟩
    rw [coverTransporter_fiber, Equiv.apply_symm_apply]
    exact hp

include transport in
/-- The actual fibre functor reflects the transporter isomorphism. -/
theorem coverTransporter_isIso : IsIso (coverTransporter s T R compatibility) := by
  let e := Equiv.ofBijective ((fiberToFinite s).map (coverTransporter s T R compatibility))
    (coverTransporter_bijective s T R compatibility transport)
  have he : (FintypeCat.equivEquivIso e).hom =
      (fiberToFinite s).map (coverTransporter s T R compatibility) := by
    apply FintypeCat.hom_ext
    intro p
    rfl
  have : IsIso ((fiberToFinite s).map (coverTransporter s T R compatibility)) := by
    rw [← he]
    infer_instance
  exact isIso_of_reflects_iso _ (fiberToFinite s)

/-- An actual scheme isomorphism, not a geometric-point-only bijection. -/
def schemeTransporterIso :
    (groupScheme s R).X ⊗ (torsorCover s T).obj ≅ (torsorCover s T).obj ⊗ (torsorCover s T).obj
      := by
  letI := coverTransporter_isIso s T R compatibility transport
  exact (forget B).mapIso (asIso (coverTransporter s T R compatibility))

theorem schemeTransporterIso_hom :
    (schemeTransporterIso s T R compatibility transport).hom =
      lift (schemeActionMap s T R compatibility) (snd (groupScheme s R).X (torsorCover s T).obj)
        := rfl

include transport in
/-- The inverse scheme transporter gives unique transport for every test
object over `B`, without any reducedness or point-surjectivity hypothesis. -/
theorem schemeTransport_unique {Y : Over B} (x y : Y ⟶ (torsorCover s T).obj) :
    ∃! a : Y ⟶ (groupScheme s R).X,
      lift a x ≫ schemeActionMap s T R compatibility = y := by
  let z : Y ⟶ (groupScheme s R).X ⊗ (torsorCover s T).obj :=
    lift y x ≫ (schemeTransporterIso s T R compatibility transport).inv
  have hz : z ≫ (schemeTransporterIso s T R compatibility transport).hom = lift y x := by
    simp only [z, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hact : z ≫ schemeActionMap s T R compatibility = y := by
    have h := congrArg (fun f => f ≫ fst (torsorCover s T).obj (torsorCover s T).obj) hz
    simpa only [schemeTransporterIso_hom, Category.assoc, lift_fst] using h
  have hx : z ≫ snd (groupScheme s R).X (torsorCover s T).obj = x := by
    have h := congrArg (fun f => f ≫ snd (torsorCover s T).obj (torsorCover s T).obj) hz
    simpa only [schemeTransporterIso_hom, Category.assoc, lift_snd] using h
  refine ⟨z ≫ fst (groupScheme s R).X (torsorCover s T).obj, ?_, ?_⟩
  · change lift (z ≫ fst (groupScheme s R).X (torsorCover s T).obj) x ≫
      schemeActionMap s T R compatibility = y
    rw [← hx, lift_comp_fst_snd]
    exact hact
  · intro a ha
    have hh : lift a x ≫ (schemeTransporterIso s T R compatibility transport).hom = lift y x := by
      rw [schemeTransporterIso_hom]
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [Category.assoc, lift_fst] using ha
      · simp only [Category.assoc, lift_snd]
    have he : lift a x = z := (cancel_mono (schemeTransporterIso s T R compatibility
      transport).hom).1
      (hh.trans hz.symm)
    have hf := congrArg (fun f => f ≫ fst (groupScheme s R).X (torsorCover s T).obj) he
    simpa only [lift_fst] using hf

/-- The existing scheme torsor-action consumer, constructed from finite actions
and finite-set torsor axioms through the actual classification theorem. -/
def schemeTorsorAction :
    TorsorAction (groupScheme s R) (toUnit (torsorCover s T).obj) where
  act a x := lift a x ≫ schemeActionMap s T R compatibility
  naturality f a x := by simp only [comp_lift_assoc]
  one_act x := by
    have h := congrArg (fun f => x ≫ f) (schemeActionMap_one s T R compatibility)
    simpa only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, Hom.one_def] using h
  mul_act a b x := by
    have h := congrArg (fun f => lift (lift a b) x ≫ f) (schemeActionMap_mul s T R compatibility)
    simpa only [comp_lift_assoc, lift_fst_assoc, lift_snd, lift_fst, Hom.mul_def] using h
  over a x := toUnit_unique _ _
  transport x y _ := schemeTransport_unique s T R compatibility transport x y

theorem schemeTorsorAction_actionMap :
    (schemeTorsorAction s T R compatibility transport).actionMap =
      schemeActionMap s T R compatibility := by
  change lift (fst (groupScheme s R).X (torsorCover s T).obj)
    (snd (groupScheme s R).X (torsorCover s T).obj) ≫ schemeActionMap s T R compatibility = _
  rw [lift_fst_snd, Category.id_comp]

/-- The resulting scheme torsor action retains the original finite-set action. -/
theorem schemeTorsorAction_fiber (a : Over.mk s ⟶ (groupScheme s R).X)
    (x : Fiber s (torsorCover s T)) :
    torsorFiberEquiv s T ((schemeTorsorAction s T R compatibility transport).act a x) =
      groupFiberMulEquiv s R a • torsorFiberEquiv s T x :=
  schemeActionMap_point s T R compatibility a x

end AlgebraicGeometry.Scheme.FiniteEtale.TorsorDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ea436c013400e3bba67ec6bc897089e5fd02b3aa8411aa92e0b464dad5193b18.
Definitions, hypotheses and universes are retained modulo native names. -/
