/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Pointed torsor actions and marked kernels

Source: `K2-018#prop:k2018-arithmetic-characters`, especially the paragraph
beginning “A primitive character is surjective”, `research/exposes/K2/018/expose.tex`
lines 426–432 at HEAD `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.

This module proves the action/translation/kernel part in an arbitrary Cartesian
category. `PointedIsogenies` specializes it to actual schemes over `Spec F`.
Points here mean morphisms from *every* test object, not merely rational points.
Transport is required only between two already existing points in one fibre;
surjectivity on all sets of test-object points is never assumed.

The only rigidity premise below concerns actual morphisms `T × X ⟶ X`. Its
geometric finite-étale justification is a separately named background input in
`PointedIsogenies`. Neither the action/kernel equivalence nor the translation
conclusion is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the natural
simply transitive action in each nonempty fibre. Geometric local nonemptiness is
separate; this definition does not posit rational lifts. -/
structure TorsorAction (A : Grp C) {X E : C} (p : X ⟶ E) where
  /-- The action of `A` on `X` on generalized points with a common test object. -/
  act : ∀ {T : C}, (T ⟶ A.X) → (T ⟶ X) → (T ⟶ X)
  naturality : ∀ {T U : C} (f : T ⟶ U) (a : U ⟶ A.X) (x : U ⟶ X),
    f ≫ act a x = act (f ≫ a) (f ≫ x)
  one_act : ∀ {T : C} (x : T ⟶ X), act 1 x = x
  mul_act : ∀ {T : C} (a b : T ⟶ A.X) (x : T ⟶ X),
    act (a * b) x = act a (act b x)
  over : ∀ {T : C} (a : T ⟶ A.X) (x : T ⟶ X), act a x ≫ p = x ≫ p
  transport : ∀ {T : C} (x y : T ⟶ X), x ≫ p = y ≫ p →
    ∃! a : T ⟶ A.X, act a x = y

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: actions
are determined by their action on every test object; all other fields are laws. -/
@[ext]
theorem TorsorAction.ext {A : Grp C} {X E : C} {p : X ⟶ E}
    (τ σ : TorsorAction A p)
    (h : ∀ (T : C) (a : T ⟶ A.X) (x : T ⟶ X), τ.act a x = σ.act a x) : τ = σ := by
  cases τ with
  | mk f fn fo fm fv ft =>
    cases σ with
    | mk g gn go gm gv gt =>
      have he : @f = @g := by funext T a x; exact h T a x
      cases he
      rfl

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: after
choosing an existing point, its fibre is equivalent to the coefficient points.
Existence of geometric points is a separate geometric input. -/
def TorsorAction.fiberEquiv {A : Grp C} {X E : C} {p : X ⟶ E}
    (τ : TorsorAction A p) {T : C} (x : T ⟶ X) :
    (T ⟶ A.X) ≃ {y : T ⟶ X // y ≫ p = x ≫ p} :=
  Equiv.ofBijective (fun a => ⟨τ.act a x, τ.over a x⟩) (by
    constructor
    · intro a b hab
      obtain ⟨c, hc, hu⟩ := τ.transport x (τ.act b x) (τ.over b x).symm
      exact (hu a (congrArg Subtype.val hab)).trans (hu b rfl).symm
    · intro y
      obtain ⟨a, ha, _⟩ := τ.transport x y.val y.property.symm
      exact ⟨a, Subtype.ext ha⟩)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
natural point action is represented by this actual ambient morphism. -/
def TorsorAction.actionMap {A : Grp C} {X E : C} {p : X ⟶ E}
    (τ : TorsorAction A p) : A.X ⊗ X ⟶ X := τ.act (fst A.X X) (snd A.X X)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
natural point action is exactly evaluation of the represented action morphism. -/
theorem TorsorAction.comp_actionMap {A : Grp C} {X E : C} {p : X ⟶ E}
    (τ : TorsorAction A p) {T : C} (a : T ⟶ A.X) (x : T ⟶ X) :
    lift a x ≫ τ.actionMap = τ.act a x := by
  simp [TorsorAction.actionMap, τ.naturality]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: natural
unique transport proves the genuine torsor pullback square
`A × X → X ×_E X`, independently of any group law on `X`. -/
theorem TorsorAction.action_isPullback {A : Grp C} {X E : C} {p : X ⟶ E}
    (τ : TorsorAction A p) : IsPullback τ.actionMap (snd A.X X) p p := by
  refine ⟨⟨τ.over _ _⟩, ⟨Limits.PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  let r := τ.transport s.snd s.fst s.condition.symm
  let a := Classical.choose r
  have ha := (Classical.choose_spec r).1
  have hu := (Classical.choose_spec r).2
  refine ⟨lift a s.snd, ?_, ?_, ?_⟩
  · exact (τ.comp_actionMap a s.snd).trans ha
  · exact lift_snd a s.snd
  · intro m hm₁ hm₂
    change m ≫ τ.actionMap = s.fst at hm₁
    change m ≫ snd A.X X = s.snd at hm₂
    apply CartesianMonoidalCategory.hom_ext
    · simp only [lift_fst]
      apply hu
      calc
        τ.act (m ≫ fst A.X X) s.snd = τ.act (m ≫ fst A.X X) (m ≫ snd A.X X) := by
          rw [hm₂]
        _ = m ≫ τ.act (fst A.X X) (snd A.X X) := (τ.naturality m _ _).symm
        _ = s.fst := hm₁
    · exact hm₂.trans (lift_snd a s.snd).symm

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the precise
parameterized lift-uniqueness premise used to identify deck maps as translations.
Every quantified map is a morphism in the ambient category. -/
def PointedLiftRigidity {X E : C} (p : X ⟶ E) (o : 𝟙_ C ⟶ X) : Prop :=
  ∀ (T : C) (f g : T ⊗ X ⟶ X),
    f ≫ p = snd T X ≫ p → g ≫ p = snd T X ≫ p →
    lift (𝟙 T) (toUnit T ≫ o) ≫ f = lift (𝟙 T) (toUnit T ≫ o) ≫ g → f = g

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: a marking
by a genuine group-object morphism with the kernel universal property on all
test objects. No geometric-point-only or constant-coefficient replacement occurs. -/
structure KernelMarking (A G E : Grp C) (p : G ⟶ E) where
  /-- The group-object morphism identifying `A` with the marked kernel of `p`. -/
  inclusion : A ⟶ G
  over : inclusion.hom.hom ≫ p.hom.hom = (1 : A.X ⟶ E.X)
  unique_lift : ∀ {T : C} (k : T ⟶ G.X), k ≫ p.hom.hom = 1 →
    ∃! a : T ⟶ A.X, a ≫ inclusion.hom.hom = k

variable {A G E : Grp C} {p : G ⟶ E}

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: a marking
is determined by its genuine group-object inclusion; other fields are proofs. -/
@[ext]
theorem KernelMarking.ext (m m' : KernelMarking A G E p)
    (h : m.inclusion = m'.inclusion) : m = m' := by
  cases m
  cases m'
  cases h
  rfl

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
universal marking exhibits the coefficient object itself as the actual kernel
pullback of the isogeny along the identity section. -/
theorem KernelMarking.isPullback (m : KernelMarking A G E p) :
    IsPullback m.inclusion.hom.hom (toUnit A.X) p.hom.hom η[E.X] := by
  refine ⟨⟨m.over⟩, ⟨Limits.PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  have hk : s.fst ≫ p.hom.hom = 1 := by
    rw [s.condition, toUnit_unique s.snd (toUnit s.pt)]
    rfl
  let r := m.unique_lift s.fst hk
  let a := Classical.choose r
  have ha := (Classical.choose_spec r).1
  have hu := (Classical.choose_spec r).2
  exact ⟨a, ha, toUnit_unique _ _, fun h _ => hu _ h⟩

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: evaluating
the action at the origin defines an actual ambient morphism from the coefficient
object to the covering group object. -/
def TorsorAction.orbit (τ : TorsorAction A p.hom.hom) : A.X ⟶ G.X :=
  τ.act (𝟙 A.X) 1

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: naturality
identifies every point of the orbit morphism with its action on the origin. -/
theorem TorsorAction.comp_orbit (τ : TorsorAction A p.hom.hom)
    {T : C} (a : T ⟶ A.X) : a ≫ τ.orbit = τ.act a 1 := by
  simpa [TorsorAction.orbit] using τ.naturality a (𝟙 A.X) (1 : A.X ⟶ G.X)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the orbit
of the origin lies in the scheme-valued kernel; the covering map is already a
group-object morphism at this step. -/
theorem TorsorAction.orbit_over (τ : TorsorAction A p.hom.hom) :
    τ.orbit ≫ p.hom.hom = (1 : A.X ⟶ E.X) := by
  simpa [TorsorAction.orbit] using τ.over (𝟙 A.X) (1 : A.X ⟶ G.X)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: lift
rigidity forces the universal deck action to be translation. This derives the
source's translation assertion from action laws and an independent morphism
rigidity premise. -/
theorem TorsorAction.translation (τ : TorsorAction A p.hom.hom)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X])
    {T : C} (a : T ⟶ A.X) (x : T ⟶ G.X) :
    τ.act a x = (a ≫ τ.orbit) * x := by
  let f : A.X ⊗ G.X ⟶ G.X := τ.act (fst A.X G.X) (snd A.X G.X)
  let g : A.X ⊗ G.X ⟶ G.X := (fst A.X G.X ≫ τ.orbit) * snd A.X G.X
  have hf : f ≫ p.hom.hom = snd A.X G.X ≫ p.hom.hom := τ.over _ _
  have hg : g ≫ p.hom.hom = snd A.X G.X ≫ p.hom.hom := by
    simp [g, MonObj.mul_comp, Category.assoc, τ.orbit_over]
  have hfg : f = g := rigidity A.X f g hf hg (by
    simp only [f, g, τ.naturality, MonObj.comp_mul,
      lift_fst, lift_snd, lift_fst_assoc, Category.id_comp]
    change τ.orbit = τ.orbit * 1
    simp)
  have h := congrArg (fun z => lift a x ≫ z) hfg
  simpa [f, g, τ.naturality, MonObj.comp_mul, Category.assoc] using h

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the action
law and the derived translation formula make the orbit map multiplicative. -/
theorem TorsorAction.orbit_mul (τ : TorsorAction A p.hom.hom)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X])
    {T : C} (a b : T ⟶ A.X) :
    (a * b) ≫ τ.orbit = (a ≫ τ.orbit) * (b ≫ τ.orbit) := by
  calc
    (a * b) ≫ τ.orbit = τ.act (a * b) 1 := τ.comp_orbit _
    _ = τ.act a (τ.act b 1) := τ.mul_act _ _ _
    _ = (a ≫ τ.orbit) * τ.act b 1 := τ.translation rigidity _ _
    _ = (a ≫ τ.orbit) * (b ≫ τ.orbit) := by rw [τ.comp_orbit b]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
coefficient-to-kernel orbit map is a genuine internal group homomorphism. -/
def TorsorAction.orbitHom (τ : TorsorAction A p.hom.hom)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X]) : A ⟶ G :=
  Grp.homMk'' τ.orbit
    (by rw [MonObj.one_eq_one, τ.comp_orbit, τ.one_act, ← MonObj.one_eq_one])
    (by
      rw [MonObj.mul_eq_mul, τ.orbit_mul rigidity]
      simp [CategoryTheory.Hom.mul_def])

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
pointed torsor action yields a descended kernel marking. The unique-lift proof
uses transport only within the origin fibre. -/
def TorsorAction.toKernelMarking (τ : TorsorAction A p.hom.hom)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X]) : KernelMarking A G E p where
  inclusion := τ.orbitHom rigidity
  over := τ.orbit_over
  unique_lift k hk := by
    obtain ⟨a, ha, hu⟩ := τ.transport (1 : _ ⟶ G.X) k (by simpa using hk.symm)
    refine ⟨a, ?_, ?_⟩
    · exact (τ.comp_orbit a).trans ha
    · intro b hb
      exact hu b ((τ.comp_orbit b).symm.trans hb)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
converse action is translation by the marked kernel. Its unique-transport proof
uses the difference `y * x⁻¹`, so it makes no global point-lifting assumption. -/
def KernelMarking.toTorsorAction (m : KernelMarking A G E p) :
    TorsorAction A p.hom.hom where
  act a x := (a ≫ m.inclusion.hom.hom) * x
  naturality f a x := by simp [MonObj.comp_mul, Category.assoc]
  one_act x := by simp
  mul_act a b x := by simp [MonObj.mul_comp, _root_.mul_assoc]
  over a x := by simp [MonObj.mul_comp, Category.assoc, m.over]
  transport x y hxy := by
    have hk : (y * x⁻¹) ≫ p.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    obtain ⟨a, ha, hu⟩ := m.unique_lift (y * x⁻¹) hk
    refine ⟨a, ?_, ?_⟩
    · change (a ≫ m.inclusion.hom.hom) * x = y
      rw [ha]
      simp [_root_.mul_assoc]
    · intro b hb
      change (b ≫ m.inclusion.hom.hom) * x = y at hb
      apply hu b
      rw [← hb]
      simp [_root_.mul_assoc]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: recovering
the translation action from its orbit marking returns the original action on
every test scheme. -/
theorem TorsorAction.marking_action (τ : TorsorAction A p.hom.hom)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X])
    {T : C} (a : T ⟶ A.X) (x : T ⟶ G.X) :
    (τ.toKernelMarking rigidity).toTorsorAction.act a x = τ.act a x :=
  (τ.translation rigidity a x).symm

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: recovering
the kernel inclusion from its translation action returns the original genuine
group-object morphism, not merely the same map on rational points. -/
theorem KernelMarking.action_marking_inclusion (m : KernelMarking A G E p)
    (rigidity : PointedLiftRigidity p.hom.hom η[G.X]) :
    (m.toTorsorAction.toKernelMarking rigidity).inclusion = m.inclusion := by
  apply Grp.hom_ext
  simp [TorsorAction.toKernelMarking, TorsorAction.orbitHom,
    TorsorAction.orbit, KernelMarking.toTorsorAction]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: for a
fixed pointed group-object cover with the separately supplied morphism rigidity,
torsor actions and kernel markings are equivalent by the proved mutually inverse
orbit and translation constructions. No equivalence is a structure field. -/
def actionKernelEquiv (rigidity : PointedLiftRigidity p.hom.hom η[G.X]) :
    TorsorAction A p.hom.hom ≃ KernelMarking A G E p where
  toFun τ := τ.toKernelMarking rigidity
  invFun m := m.toTorsorAction
  left_inv τ := TorsorAction.ext _ _ (fun _ a x => τ.marking_action rigidity a x)
  right_inv m := KernelMarking.ext _ _ (m.action_marking_inclusion rigidity)

end CategoryTheory

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 83aa4192b4f0048586bad85fdb317e996149f18c185ad8cd1ba9667965dd422b.
Definitions, hypotheses and universes are retained modulo native names. -/
