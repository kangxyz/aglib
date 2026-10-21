/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction

/-!
# Actual scheme actions representing finite sheaf torsors

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Morphisms are recovered by
Yoneda evaluation on finite étale test schemes. The action and difference
morphisms then extend the sheaf torsor action to every scheme test object.
No morphism, product, action, or classification comparison is a premise.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] Over.cartesianMonoidalCategory
  Scheme.FiniteEtale.GroupDescent.coverCartesian
variable {X : Scheme.{u}}

/-- Postcomposition of genuine finite étale scheme sections. -/
def finiteRepresentedSetSheafMap {Y Z : Scheme.FiniteEtale X} (f : Y.obj ⟶ Z.obj) :
    finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z where
  hom := {
    app U := ↾fun s => ULift.up (s.down ≫ f)
    naturality {U V} g := by ext s; exact congrArg ULift.up (Category.assoc _ _ _) }

/-- The small-site Yoneda inverse evaluates on the identity section of Y. -/
def finiteRepresentedSetSheafPreimage {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) : Y.obj ⟶ Z.obj :=
  (q.hom.app (op ((toEtale X).obj Y)) (ULift.up (𝟙 Y.obj))).down

@[simp] theorem finiteRepresentedSetSheafPreimage_map {Y Z : Scheme.FiniteEtale X}
    (f : Y.obj ⟶ Z.obj) :
    finiteRepresentedSetSheafPreimage (finiteRepresentedSetSheafMap f) = f :=
  Category.id_comp f

/-- Naturality recovers every component from the identity section. -/
theorem finiteRepresentedSetSheafMap_preimage {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) :
    finiteRepresentedSetSheafMap (finiteRepresentedSetSheafPreimage q) = q := by
  ext U s
  let f : U.unop ⟶ (toEtale X).obj Y :=
    MorphismProperty.Over.homMk s.down.left (Over.w s.down) (by trivial)
  have h := congrFun (congrArg (fun k => k.hom) (q.hom.naturality f.op))
    (ULift.up (𝟙 Y.obj))
  change q.hom.app U (ULift.up (s.down ≫ 𝟙 Y.obj)) = ULift.up (s.down ≫ _) at h
  rw [Category.comp_id] at h
  cases s
  exact h.symm

/-- Full faithfulness is a proved Yoneda equivalence, not a representability premise. -/
def finiteRepresentedSetSheafHomEquiv (Y Z : Scheme.FiniteEtale X) :
    (Y.obj ⟶ Z.obj) ≃ (finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z) where
  toFun := finiteRepresentedSetSheafMap
  invFun := finiteRepresentedSetSheafPreimage
  left_inv := finiteRepresentedSetSheafPreimage_map
  right_inv := finiteRepresentedSetSheafMap_preimage

@[simp] theorem finiteRepresentedSetSheafMap_id (Y : Scheme.FiniteEtale X) :
    finiteRepresentedSetSheafMap (𝟙 Y.obj) = 𝟙 _ := by ext U s; cases s; simp
      [finiteRepresentedSetSheafMap]

@[simp] theorem finiteRepresentedSetSheafMap_comp {Y Z W : Scheme.FiniteEtale X}
    (f : Y.obj ⟶ Z.obj) (g : Z.obj ⟶ W.obj) :
    finiteRepresentedSetSheafMap (f ≫ g) =
      finiteRepresentedSetSheafMap f ≫ finiteRepresentedSetSheafMap g := by
  ext U s
  exact congrArg ULift.up (Category.assoc _ _ _).symm

/-- Yoneda sends an actual scheme isomorphism to an actual set-sheaf isomorphism. -/
def finiteRepresentedSetSheafMapIso {Y Z : Scheme.FiniteEtale X} (e : Y.obj ≅ Z.obj) :
    finiteRepresentedSetSheaf Y ≅ finiteRepresentedSetSheaf Z where
  hom := finiteRepresentedSetSheafMap e.hom
  inv := finiteRepresentedSetSheafMap e.inv
  hom_inv_id := by rw [← finiteRepresentedSetSheafMap_comp, e.hom_inv_id,
    finiteRepresentedSetSheafMap_id]
  inv_hom_id := by rw [← finiteRepresentedSetSheafMap_comp, e.inv_hom_id,
    finiteRepresentedSetSheafMap_id]

/-- An actual sheaf isomorphism uniquely determines an actual scheme isomorphism. -/
def finiteRepresentedSetSheafIso {Y Z : Scheme.FiniteEtale X}
    (e : finiteRepresentedSetSheaf Y ≅ finiteRepresentedSetSheaf Z) : Y.obj ≅ Z.obj where
  hom := finiteRepresentedSetSheafPreimage e.hom
  inv := finiteRepresentedSetSheafPreimage e.inv
  hom_inv_id := by
    apply (finiteRepresentedSetSheafHomEquiv Y Y).injective
    change finiteRepresentedSetSheafMap (_ ≫ _) = finiteRepresentedSetSheafMap _
    rw [finiteRepresentedSetSheafMap_comp, finiteRepresentedSetSheafMap_preimage,
      finiteRepresentedSetSheafMap_preimage, finiteRepresentedSetSheafMap_id, e.hom_inv_id]
  inv_hom_id := by
    apply (finiteRepresentedSetSheafHomEquiv Z Z).injective
    change finiteRepresentedSetSheafMap (_ ≫ _) = finiteRepresentedSetSheafMap _
    rw [finiteRepresentedSetSheafMap_comp, finiteRepresentedSetSheafMap_preimage,
      finiteRepresentedSetSheafMap_preimage, finiteRepresentedSetSheafMap_id, e.inv_hom_id]

/-- Exact evaluation formula for the recovered Yoneda morphism. -/
theorem finiteRepresentedSetSheafPreimage_app {Y Z : Scheme.FiniteEtale X}
    (q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z)
    (U : X.Etale) (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    ULift.up (x ≫ finiteRepresentedSetSheafPreimage q) = q.hom.app (op U) (ULift.up x) :=
  congrArg (fun r : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Z =>
    r.hom.app (op U) (ULift.up x)) (finiteRepresentedSetSheafMap_preimage q)

namespace Torsor
variable (H : Grp (Over X)) [IsCommMonObj H.X]
variable (P : Torsor (representedSheaf H)) (Y : Scheme.FiniteEtale X)
variable (e : finiteRepresentedSetSheaf Y ≅ P.carrier)

/-- Represented sections identified with the actual torsor sections. -/
def representedSectionEquiv (U : X.Etale) :
    (((Scheme.Etale.forget X).obj U) ⟶ Y.obj) ≃ P.carrier.obj.obj (op U) where
  toFun x := e.hom.hom.app (op U) (ULift.up x)
  invFun t := (e.inv.hom.app (op U) t).down
  left_inv x := congrArg (fun q : finiteRepresentedSetSheaf Y ⟶ finiteRepresentedSetSheaf Y =>
    (q.hom.app (op U) (ULift.up x)).down) e.hom_inv_id
  right_inv t := congrArg (fun q : P.carrier ⟶ P.carrier => q.hom.app (op U) t) e.inv_hom_id

/-- Naturality of the actual representative's section identification. -/
theorem representedSectionEquiv_naturality {U V : X.Etale} (f : U ⟶ V)
    (x : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    P.representedSectionEquiv H Y e U ((Scheme.Etale.forget X).map f ≫ x) =
      P.carrier.obj.map f.op (P.representedSectionEquiv H Y e V x) :=
  congrArg (fun q : (finiteRepresentedSetSheaf Y).obj.obj (op V) ⟶
    P.carrier.obj.obj (op U) => q (ULift.up x)) (e.hom.hom.naturality f.op)

/-- The action on étale test objects, before its extension to all schemes. -/
def representedEtaleAction (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (Scheme.Etale.forget X).obj U ⟶ Y.obj :=
  (P.representedSectionEquiv H Y e U).symm
    (P.action (op U) (ULift.up (Additive.ofMul a)) (P.representedSectionEquiv H Y e U x))

theorem representedEtaleAction_naturality {U V : X.Etale} (f : U ⟶ V)
    (a : (Scheme.Etale.forget X).obj V ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj V ⟶ Y.obj) :
    (Scheme.Etale.forget X).map f ≫ P.representedEtaleAction H Y e V a x =
      P.representedEtaleAction H Y e U ((Scheme.Etale.forget X).map f ≫ a)
        ((Scheme.Etale.forget X).map f ≫ x) := by
  apply (P.representedSectionEquiv H Y e U).injective
  rw [P.representedSectionEquiv_naturality]
  simp only [representedEtaleAction, Equiv.apply_symm_apply]
  rw [P.naturality, P.representedSectionEquiv_naturality]
  rfl

theorem representedEtaleAction_one (U : X.Etale)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedEtaleAction H Y e U 1 x = x := by
  apply (P.representedSectionEquiv H Y e U).injective
  simp only [representedEtaleAction, Equiv.apply_symm_apply]
  exact P.zero_action _ _

theorem representedEtaleAction_mul (U : X.Etale)
    (a b : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedEtaleAction H Y e U (a * b) x =
      P.representedEtaleAction H Y e U a (P.representedEtaleAction H Y e U b x) := by
  apply (P.representedSectionEquiv H Y e U).injective
  simp only [representedEtaleAction, Equiv.apply_symm_apply]
  exact P.add_action _ _ _ _

/-- Simply transitive transport on actual étale test objects. -/
theorem representedEtaleAction_transport (U : X.Etale)
    (x y : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    ∃! a, P.representedEtaleAction H Y e U a x = y := by
  obtain ⟨a, ha, hu⟩ := P.unique_transport (op U)
    (P.representedSectionEquiv H Y e U x) (P.representedSectionEquiv H Y e U y)
  refine ⟨a.down.toMul, ?_, ?_⟩
  · apply (P.representedSectionEquiv H Y e U).injective
    cases a
    simpa only [representedEtaleAction, Equiv.apply_symm_apply, ofMul_toMul] using ha
  · intro b hb
    have he := congrArg (P.representedSectionEquiv H Y e U) hb
    simp only [representedEtaleAction, Equiv.apply_symm_apply] at he
    exact congrArg (fun a => a.down.toMul) (hu (ULift.up (Additive.ofMul b)) he)

variable [IsFinite H.X.hom] [Etale H.X.hom]

/-- The actual finite étale product on which the universal action is evaluated. -/
abbrev representedActionDomain : Scheme.FiniteEtale X :=
  Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H ⊗ Y

/-- The genuine scheme action morphism recovered on the universal étale test. -/
def representedActionMap : H.X ⊗ Y.obj ⟶ Y.obj :=
  P.representedEtaleAction H Y e ((toEtale X).obj (representedActionDomain H Y))
    (fst H.X Y.obj) (snd H.X Y.obj)

/-- Evaluation of the actual action morphism on an arbitrary scheme over X. -/
def representedAct {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) : T ⟶ Y.obj :=
  lift a x ≫ P.representedActionMap H Y e

theorem representedAct_naturality {T U : Over X} (f : T ⟶ U)
    (a : U ⟶ H.X) (x : U ⟶ Y.obj) :
    f ≫ P.representedAct H Y e a x = P.representedAct H Y e (f ≫ a) (f ≫ x) := by
  simp [representedAct, ← comp_lift, Category.assoc]

/-- The extended scheme action agrees with the original sheaf action on every
étale test scheme, by naturality on the universal product. -/
theorem representedAct_eq_etale (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    P.representedAct H Y e a x = P.representedEtaleAction H Y e U a x := by
  let f : U ⟶ (toEtale X).obj (representedActionDomain H Y) :=
    MorphismProperty.Over.homMk (lift a x).left (Over.w _) (by trivial)
  have h := P.representedEtaleAction_naturality H Y e f (fst H.X Y.obj) (snd H.X Y.obj)
  change lift a x ≫ P.representedActionMap H Y e =
    P.representedEtaleAction H Y e U (lift a x ≫ fst H.X Y.obj)
      (lift a x ≫ snd H.X Y.obj) at h
  simpa only [representedAct, lift_fst, lift_snd] using h

theorem representedAct_one {T : Over X} (x : T ⟶ Y.obj) :
    P.representedAct H Y e 1 x = x := by
  have h : P.representedAct H Y e 1 (𝟙 Y.obj) = 𝟙 Y.obj := by
    rw [P.representedAct_eq_etale H Y e ((toEtale X).obj Y)]
    exact P.representedEtaleAction_one H Y e _ _
  have hh := congrArg (fun q => x ≫ q) h
  simpa only [P.representedAct_naturality, comp_one, Category.comp_id] using hh

theorem representedAct_mul {T : Over X} (a b : T ⟶ H.X) (x : T ⟶ Y.obj) :
    P.representedAct H Y e (a * b) x =
      P.representedAct H Y e a (P.representedAct H Y e b x) := by
  let C := Scheme.FiniteEtale.FiberTorsorActions.coefficientCover H
  let Z : Scheme.FiniteEtale X := (C ⊗ C) ⊗ Y
  let a' : Z.obj ⟶ H.X := fst (H.X ⊗ H.X) Y.obj ≫ fst H.X H.X
  let b' : Z.obj ⟶ H.X := fst (H.X ⊗ H.X) Y.obj ≫ snd H.X H.X
  let x' : Z.obj ⟶ Y.obj := snd (H.X ⊗ H.X) Y.obj
  have h : P.representedAct H Y e (a' * b') x' =
      P.representedAct H Y e a' (P.representedAct H Y e b' x') := by
    simp only [P.representedAct_eq_etale H Y e ((toEtale X).obj Z)]
    exact P.representedEtaleAction_mul H Y e _ _ _ _
  have hh := congrArg (fun q => lift (lift a b) x ≫ q) h
  simpa only [P.representedAct_naturality, comp_mul, a', b', x',
    lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc] using hh

/-- The actual difference morphism is obtained from unique transport on Y×Y. -/
def representedDifferenceMap : Y.obj ⊗ Y.obj ⟶ H.X :=
  Classical.choose (P.representedEtaleAction_transport H Y e
    ((toEtale X).obj (Y ⊗ Y)) (fst Y.obj Y.obj) (snd Y.obj Y.obj))

/-- The morphism `T ⟶ H.X` obtained by applying the represented difference map to the pair
`(x, y)` . -/
def representedDifference {T : Over X} (x y : T ⟶ Y.obj) : T ⟶ H.X :=
  lift x y ≫ P.representedDifferenceMap H Y e

omit [IsFinite H.X.hom] [Etale H.X.hom] in
theorem representedDifference_naturality {T U : Over X} (f : T ⟶ U)
    (x y : U ⟶ Y.obj) :
    f ≫ P.representedDifference H Y e x y =
      P.representedDifference H Y e (f ≫ x) (f ≫ y) := by
  simp [representedDifference, ← comp_lift, Category.assoc]

/-- The difference morphism produces transport on all scheme test objects. -/
theorem representedAct_difference {T : Over X} (x y : T ⟶ Y.obj) :
    P.representedAct H Y e (P.representedDifference H Y e x y) x = y := by
  have h : P.representedAct H Y e (P.representedDifferenceMap H Y e)
      (fst Y.obj Y.obj) = snd Y.obj Y.obj := by
    rw [P.representedAct_eq_etale H Y e ((toEtale X).obj (Y ⊗ Y))]
    exact (Classical.choose_spec (P.representedEtaleAction_transport H Y e
      ((toEtale X).obj (Y ⊗ Y)) (fst Y.obj Y.obj) (snd Y.obj Y.obj))).1
  have hh := congrArg (fun q => lift x y ≫ q) h
  simpa only [P.representedAct_naturality, representedDifference, lift_fst, lift_snd] using hh

/-- Uniqueness too extends from the universal finite étale product to every
scheme test object; no geometric-point-only test is used. -/
theorem representedDifference_act {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) :
    P.representedDifference H Y e x (P.representedAct H Y e a x) = a := by
  let Z := representedActionDomain H Y
  let a' : Z.obj ⟶ H.X := fst H.X Y.obj
  let x' : Z.obj ⟶ Y.obj := snd H.X Y.obj
  have h : P.representedDifference H Y e x' (P.representedAct H Y e a' x') = a' := by
    apply (P.representedEtaleAction_transport H Y e ((toEtale X).obj Z)
      x' (P.representedAct H Y e a' x')).unique
    · rw [← P.representedAct_eq_etale H Y e ((toEtale X).obj Z)]
      exact P.representedAct_difference H Y e _ _
    · exact (P.representedAct_eq_etale H Y e ((toEtale X).obj Z) a' x').symm
  have hh := congrArg (fun q => lift a x ≫ q) h
  simpa only [P.representedDifference_naturality, P.representedAct_naturality,
    a', x', lift_fst, lift_snd] using hh

/-- The genuine sheaf action yields an actual scheme torsor action on all
scheme-valued points, suitable for `FiberTorsorActions.rho`. -/
def representedSchemeAction : TorsorAction H (toUnit Y.obj) where
  act := P.representedAct H Y e
  naturality := P.representedAct_naturality H Y e
  one_act := P.representedAct_one H Y e
  mul_act := P.representedAct_mul H Y e
  over _ _ := toUnit_unique _ _
  transport x y _ := ⟨P.representedDifference H Y e x y,
    P.representedAct_difference H Y e x y, fun a ha => by
      rw [← ha]
      exact (P.representedDifference_act H Y e a x).symm⟩

/-- The A3 representative carries the transported actual scheme torsor action. -/
def finiteEtaleSchemeAction (h : Stacks03RV X)
    (hL : IsFiniteLocallyConstant (representedSheaf H)) :
    TorsorAction H (toUnit (P.finiteEtaleRepresentative h hL).obj) :=
  P.representedSchemeAction H (P.finiteEtaleRepresentative h hL)
    (P.finiteEtaleRepresentativeIso h hL)

/-- Exact evaluation of the represented scheme action on the original sheaf
sections. This is the action comparison, rather than an arbitrary bijection. -/
theorem representedSchemeAction_section (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    e.hom.hom.app (op U) (ULift.up ((P.representedSchemeAction H Y e).act a x)) =
      P.action (op U) (ULift.up (Additive.ofMul a)) (e.hom.hom.app (op U) (ULift.up x)) := by
  change P.representedSectionEquiv H Y e U (P.representedAct H Y e a x) = _
  rw [P.representedAct_eq_etale]
  exact (P.representedSectionEquiv H Y e U).apply_symm_apply _

omit [IsFinite H.X.hom] [Etale H.X.hom] in
include P e in
/-- Local nonemptiness forces the actual representing finite étale scheme to
be surjective, without a rational-point surjectivity assertion. -/
theorem represented_surjective : Surjective Y.obj.hom := by
  constructor
  intro x
  have h := P.locally_nonempty (etaleTerminal X)
  change _ ∈ X.smallGrothendieckTopology @Etale (etaleTerminal X) at h
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at h
  obtain ⟨V, f, v, ⟨t⟩, _, hv⟩ := h x
  let q := (e.inv.hom.app (op V) t).down
  refine ⟨q.left v, ?_⟩
  have hq := Over.w q
  have hf := MorphismProperty.Over.w f
  have hh : q.left ≫ Y.obj.hom = f.left := by simpa using hq.trans hf.symm
  change (q.left ≫ Y.obj.hom) v = x
  rw [hh]
  exact hv

variable (Q : Torsor (representedSheaf H)) (Z : Scheme.FiniteEtale X)
variable (d : P.Iso Q) (f : finiteRepresentedSetSheaf Z ≅ Q.carrier)

/-- A torsor isomorphism determines an actual scheme isomorphism of its
finite representatives, through the proved Yoneda transport. -/
def representedIso : Y.obj ≅ Z.obj :=
  finiteRepresentedSetSheafIso (e ≪≫ d.carrierIso ≪≫ f.symm)

omit [IsFinite H.X.hom] [Etale H.X.hom] in
theorem representedIso_section (U : X.Etale)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    f.hom.hom.app (op U) (ULift.up (x ≫ (P.representedIso H Y e Q Z d f).hom)) =
      d.carrierIso.hom.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)) := by
  have h := finiteRepresentedSetSheafPreimage_app (e.hom ≫ d.carrierIso.hom ≫ f.inv) U x
  change ULift.up (x ≫ (P.representedIso H Y e Q Z d f).hom) =
    f.inv.hom.app (op U) (d.carrierIso.hom.hom.app (op U)
      (e.hom.hom.app (op U) (ULift.up x))) at h
  rw [h]
  exact congrArg (fun r : Q.carrier ⟶ Q.carrier => r.hom.app (op U)
    (d.carrierIso.hom.hom.app (op U) (e.hom.hom.app (op U) (ULift.up x)))) f.inv_hom_id

/-- The representative isomorphism respects the action on every étale test. -/
theorem representedIso_equivariant_etale (U : X.Etale)
    (a : (Scheme.Etale.forget X).obj U ⟶ H.X)
    (x : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    (P.representedSchemeAction H Y e).act a x ≫ (P.representedIso H Y e Q Z d f).hom =
      (Q.representedSchemeAction H Z f).act a (x ≫ (P.representedIso H Y e Q Z d f).hom) := by
  apply (Q.representedSectionEquiv H Z f U).injective
  change f.hom.hom.app (op U) (ULift.up _) = f.hom.hom.app (op U) (ULift.up _)
  rw [P.representedIso_section, P.representedSchemeAction_section,
    Q.representedSchemeAction_section, P.representedIso_section, d.equivariant]

/-- Equivariance holds on every scheme-valued point, in particular on the
actual geometric fibres consumed by finite-cover monodromy. -/
theorem representedIso_equivariant {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj) :
    (P.representedSchemeAction H Y e).act a x ≫ (P.representedIso H Y e Q Z d f).hom =
      (Q.representedSchemeAction H Z f).act a (x ≫ (P.representedIso H Y e Q Z d f).hom) := by
  have h := P.representedIso_equivariant_etale H Y e Q Z d f
    ((toEtale X).obj (representedActionDomain H Y)) (fst H.X Y.obj) (snd H.X Y.obj)
  have hh := congrArg (fun q => lift a x ≫ q) h
  simpa only [← Category.assoc, TorsorAction.naturality, lift_fst, lift_snd,
    lift_snd_assoc] using hh

end Torsor
/-- A surjective finite étale representative is locally inhabited on the
actual small étale site, by its actual pullback cover. -/
theorem finiteRepresentedSetSheaf_locally_nonempty (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] (U : X.Etale) :
    nonemptySieve (finiteRepresentedSetSheaf Y) U ∈ Scheme.smallEtaleTopology X U := by
  change _ ∈ X.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  let V : X.Etale := Scheme.Etale.mk (pullback.snd Y.obj.hom U.hom ≫ U.hom)
  let f : V ⟶ U := MorphismProperty.Over.homMk (pullback.snd Y.obj.hom U.hom) rfl (by trivial)
  obtain ⟨y, hy⟩ := (surjective_iff (pullback.snd Y.obj.hom U.hom)).mp inferInstance x
  refine ⟨V, f, y, ?_, inferInstanceAs (Etale (pullback.snd Y.obj.hom U.hom)), hy⟩
  exact ⟨ULift.up (Over.homMk (pullback.fst Y.obj.hom U.hom) pullback.condition)⟩

/-- Every actual surjective finite étale scheme torsor defines a genuine sheaf
torsor for the represented coefficient sheaf. -/
def torsorOfSchemeAction (H : Grp (Over X)) [IsCommMonObj H.X] (Y : Scheme.FiniteEtale X)
    [Surjective Y.obj.hom] (τ : TorsorAction H (toUnit Y.obj)) :
    Torsor (representedSheaf H) where
  carrier := finiteRepresentedSetSheaf Y
  action _ a t := ULift.up (τ.act a.down.toMul t.down)
  zero_action _ t := by cases t; apply congrArg ULift.up; exact τ.one_act _
  add_action _ a b t := congrArg ULift.up (τ.mul_act _ _ _)
  naturality f a t := congrArg ULift.up (τ.naturality ((Scheme.Etale.forget X).map f.unop) _ _)
  unique_transport _ s t := by
    obtain ⟨a, ha, hu⟩ := τ.transport s.down t.down (toUnit_unique _ _)
    refine ⟨ULift.up (Additive.ofMul a), congrArg ULift.up ha, ?_⟩
    intro b hb
    apply ULift.ext
    exact congrArg Additive.ofMul (hu b.down.toMul (congrArg ULift.down hb))
  locally_nonempty := finiteRepresentedSetSheaf_locally_nonempty Y

/-- Recovering the sheaf torsor after extending its action to all schemes
returns the original torsor by its given representative isomorphism. -/
def Torsor.representedSchemeActionIso (H : Grp (Over X)) [IsCommMonObj H.X]
    [IsFinite H.X.hom] [Etale H.X.hom] (P : Torsor (representedSheaf H))
    (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom]
      (e : finiteRepresentedSetSheaf Y ≅ P.carrier) :
    Torsor.Iso (torsorOfSchemeAction H Y (P.representedSchemeAction H Y e)) P where
  carrierIso := e
  equivariant U a t := by
    exact P.representedSchemeAction_section H Y e U.unop a.down.toMul t.down

/-- Starting from an actual scheme torsor recovers the same action on every
scheme-valued point, not just geometric or small-site points. -/
theorem torsorOfSchemeAction_representedSchemeAction (H : Grp (Over X)) [IsCommMonObj H.X]
    [IsFinite H.X.hom] [Etale H.X.hom] (Y : Scheme.FiniteEtale X) [Surjective Y.obj.hom]
    (τ : TorsorAction H (toUnit Y.obj)) :
    (torsorOfSchemeAction H Y τ).representedSchemeAction H Y (Iso.refl _) = τ := by
  apply TorsorAction.ext
  intro T a x
  change lift a x ≫ τ.act (fst H.X Y.obj) (snd H.X Y.obj) = τ.act a x
  exact τ.comp_actionMap a x

/-- A genuine equivariant scheme isomorphism gives the corresponding sheaf
torsor isomorphism, with its actual Yoneda map as carrier map. -/
def torsorOfSchemeActionIso (H : Grp (Over X)) [IsCommMonObj H.X]
    (Y Z : Scheme.FiniteEtale X) [Surjective Y.obj.hom] [Surjective Z.obj.hom]
    (τ : TorsorAction H (toUnit Y.obj)) (σ : TorsorAction H (toUnit Z.obj))
    (q : Y.obj ≅ Z.obj)
    (hq : ∀ {T : Over X} (a : T ⟶ H.X) (x : T ⟶ Y.obj),
      τ.act a x ≫ q.hom = σ.act a (x ≫ q.hom)) :
    Torsor.Iso (torsorOfSchemeAction H Y τ) (torsorOfSchemeAction H Z σ) where
  carrierIso := finiteRepresentedSetSheafMapIso q
  equivariant _ a t := congrArg ULift.up (hq a.down.toMul t.down)

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 13490df8d3617a248ab764a93311a38812036cca18d4ed7fb16852488dddffa0.
Definitions, hypotheses and universes are retained modulo native names. -/
