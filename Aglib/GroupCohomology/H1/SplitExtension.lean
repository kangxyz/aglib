/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Tactic.Abel
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Aglib.GroupCohomology.H1.Continuous
public import Mathlib.Algebra.Group.PUnit

/-!
# Pointed continuous degree-one cocycles

Source: `K2-018#eq:k2018-pointed-character`,
`research/exposes/K2/018/expose.tex`, lines 341–355, at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

This file proves the continuous cocycle calculation for a split extension in
coordinates `(u, g) * (v, h) = (u * g • v, g * h)`. The geometric subgroup acts
trivially on the additive coefficient group. Continuity is part of every
cocycle and character; ordinary discrete group cohomology is not substituted.
When the groups and actions are continuous, these are the inhomogeneous
cocycles of the topological semidirect product. The normalization and
cohomology relation below identify this coordinate model with the shared
`R5Lab.Galois.ContinuousH1` quotient, using the actual semidirect group and
inflated coefficient action. Section restriction and its kernel equivalence
with continuous characters are derived on that same common H¹ group.

No comparison with mathlib's continuous-cohomology complex, étale H¹, an
arithmetic fundamental group, or elliptic-curve isogenies is proved here.
Each declaration's source pointer below uses the module source snapshot above.
-/

@[expose] public section

namespace GroupCohomology.PointedCohomology

variable (G N A : Type*) [Group G] [Group N] [AddCommGroup A]
  [MulDistribMulAction G N] [DistribMulAction G A]
  [TopologicalSpace G] [TopologicalSpace N] [TopologicalSpace A]

/-- Direct continuous cocycle model for `K2-018#eq:k2018-pointed-character`,
on the module source basis. The geometric action on coefficients is trivial. -/
structure ContinuousCocycle where
  /-- Continuous cochain in split coordinates for `K2-018#eq:k2018-pointed-character`. -/
  toFun : N × G → A
  /-- Continuity condition for `K2-018#eq:k2018-pointed-character`. -/
  continuous_toFun : Continuous toFun
  /-- Crossed-homomorphism equation for `K2-018#eq:k2018-pointed-character`. -/
  cocycle : ∀ u v : N, ∀ g h : G,
    toFun (u * g • v, g * h) = toFun (u, g) + g • toFun (v, h)

/-- The continuous equivariant homomorphism side of
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
structure EquivariantCharacter where
  /-- Geometric character in `K2-018#eq:k2018-pointed-character`. -/
  toFun : N → A
  /-- Character continuity in `K2-018#eq:k2018-pointed-character`. -/
  continuous_toFun : Continuous toFun
  /-- Homomorphism condition in `K2-018#eq:k2018-pointed-character`. -/
  map_mul : ∀ u v : N, toFun (u * v) = toFun u + toFun v
  /-- Galois equivariance in `K2-018#eq:k2018-pointed-character`. -/
  map_action : ∀ g : G, ∀ u : N, toFun (g • u) = g • toFun u

variable {G N A}

/-- Auxiliary cocycle extensionality for `K2-018#eq:k2018-pointed-character`;
not a separately stated TeX assertion. Uses the module source basis. -/
@[ext]
theorem ContinuousCocycle.ext (c d : ContinuousCocycle G N A)
    (h : ∀ x, c.toFun x = d.toFun x) : c = d := by
  cases c with
  | mk cf cc ce =>
    cases d with
    | mk df dc de =>
      have hfun : cf = df := funext h
      subst df
      rfl

omit [TopologicalSpace G] in
/-- Auxiliary character extensionality for `K2-018#eq:k2018-pointed-character`;
not a separately stated TeX assertion. Uses the module source basis. -/
@[ext]
theorem EquivariantCharacter.ext (f k : EquivariantCharacter G N A)
    (h : ∀ u, f.toFun u = k.toFun u) : f = k := by
  cases f with
  | mk ff fc fm fa =>
    cases k with
    | mk kf kc km ka =>
      have hfun : ff = kf := funext h
      subst kf
      rfl

/-- Section normalization in `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
def ContinuousCocycle.Pointed (c : ContinuousCocycle G N A) : Prop :=
  ∀ g : G, c.toFun (1, g) = 0

/-- The section-independent representative in `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem ContinuousCocycle.pointed_value (c : ContinuousCocycle G N A)
    (hc : c.Pointed) (u : N) (g : G) :
    c.toFun (u, g) = c.toFun (u, 1) := by
  simpa [hc g] using c.cocycle u 1 1 g

omit [TopologicalSpace G] in
/-- Auxiliary identity value for `K2-018#eq:k2018-pointed-character`;
not a separately stated TeX assertion. Uses the module source basis. -/
theorem EquivariantCharacter.map_one (f : EquivariantCharacter G N A) :
    f.toFun 1 = 0 := by
  have h : f.toFun 1 + f.toFun 1 = f.toFun 1 + 0 := by
    simpa using (f.map_mul 1 1).symm
  exact add_left_cancel h

/-- Restriction direction of `K2-018#eq:k2018-pointed-character`,
on the module source basis, at the continuous cocycle level. -/
def ContinuousCocycle.restrict (c : ContinuousCocycle G N A) (hc : c.Pointed) :
    EquivariantCharacter G N A where
  toFun u := c.toFun (u, 1)
  continuous_toFun := c.continuous_toFun.comp
    (continuous_id.prodMk continuous_const)
  map_mul u v := by simpa using c.cocycle u v 1 1
  map_action g u := by
    calc
      c.toFun (g • u, 1) = c.toFun (g • u, g) :=
        (c.pointed_value hc (g • u) g).symm
      _ = g • c.toFun (u, 1) := by simpa [hc g] using c.cocycle 1 u g 1

/-- Extension direction of `K2-018#eq:k2018-pointed-character`,
on the module source basis: ignore the section coordinate. -/
def EquivariantCharacter.extend (f : EquivariantCharacter G N A) :
    ContinuousCocycle G N A where
  toFun x := f.toFun x.1
  continuous_toFun := f.continuous_toFun.comp continuous_fst
  cocycle u v g h := by
    change f.toFun (u * g • v) = f.toFun u + g • f.toFun v
    rw [f.map_mul, f.map_action]

/-- The extension in `K2-018#eq:k2018-pointed-character` is section-normalized,
on the module source basis. -/
theorem EquivariantCharacter.extend_pointed (f : EquivariantCharacter G N A) :
    f.extend.Pointed := fun _ => f.map_one

/-- The continuous cocycle calculation of `K2-018#eq:k2018-pointed-character`,
on the module source basis. The étale realization is pending. -/
def pointedCocycleEquiv :
    {c : ContinuousCocycle G N A // c.Pointed} ≃ EquivariantCharacter G N A where
  toFun c := c.1.restrict c.2
  invFun f := ⟨f.extend, f.extend_pointed⟩
  left_inv c := by
    apply Subtype.ext
    apply ContinuousCocycle.ext
    intro x
    exact (c.1.pointed_value c.2 x.1 x.2).symm
  right_inv f := by
    apply EquivariantCharacter.ext
    intro u
    rfl

/-- Direct degree-one coboundary relation for `K2-018#eq:k2018-pointed-character`,
on the module source basis; the geometric group acts trivially on coefficients. -/
def ContinuousCocycle.Cohomologous (c d : ContinuousCocycle G N A) : Prop :=
  ∃ a : A, ∀ u : N, ∀ g : G,
    d.toFun (u, g) = c.toFun (u, g) + (g • a - a)

/-- Auxiliary reflexivity for `K2-018#eq:k2018-pointed-character`'s cocycle model;
not a separately stated TeX assertion. Uses the module source basis. -/
theorem ContinuousCocycle.Cohomologous.refl (c : ContinuousCocycle G N A) :
    c.Cohomologous c := ⟨0, fun _ _ => by simp⟩

/-- Auxiliary symmetry for `K2-018#eq:k2018-pointed-character`'s cocycle model;
not a separately stated TeX assertion. Uses the module source basis. -/
theorem ContinuousCocycle.Cohomologous.symm {c d : ContinuousCocycle G N A}
    (h : c.Cohomologous d) : d.Cohomologous c := by
  obtain ⟨a, ha⟩ := h
  refine ⟨-a, ?_⟩
  intro u g
  rw [ha, smul_neg]
  abel

/-- Auxiliary transitivity for `K2-018#eq:k2018-pointed-character`'s cocycle model;
not a separately stated TeX assertion. Uses the module source basis. -/
theorem ContinuousCocycle.Cohomologous.trans {c d e : ContinuousCocycle G N A}
    (hcd : c.Cohomologous d) (hde : d.Cohomologous e) : c.Cohomologous e := by
  obtain ⟨a, ha⟩ := hcd
  obtain ⟨b, hb⟩ := hde
  refine ⟨a + b, ?_⟩
  intro u g
  rw [hb, ha, smul_add]
  abel

/-- Uniqueness of normalized representatives in `K2-018#eq:k2018-pointed-character`,
on the module source basis, in the direct continuous cocycle model. -/
theorem pointed_cohomologous_iff_eq (c d : ContinuousCocycle G N A)
    (hc : c.Pointed) (hd : d.Pointed) : c.Cohomologous d ↔ c = d := by
  constructor
  · rintro ⟨a, ha⟩
    have hinv (g : G) : g • a - a = 0 := by
      simpa [hc g, hd g] using (ha 1 g).symm
    apply ContinuousCocycle.ext
    rintro ⟨u, g⟩
    simpa [hinv g] using (ha u g).symm
  · intro h
    subst d
    exact ⟨0, fun _ _ => by simp⟩

section Normalization

variable [IsTopologicalAddGroup A] [ContinuousSMul G A]

/-- Coboundary subtraction in `K2-018#eq:k2018-pointed-character`,
on the module source basis, with continuous coefficient action. -/
def ContinuousCocycle.normalize (c : ContinuousCocycle G N A) (a : A) :
    ContinuousCocycle G N A where
  toFun x := c.toFun x - (x.2 • a - a)
  continuous_toFun := c.continuous_toFun.sub
    ((continuous_snd.smul continuous_const).sub continuous_const)
  cocycle u v g h := by
    simp only [c.cocycle, mul_smul, smul_sub]
    abel

/-- Existence of section-normalized representatives in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem ContinuousCocycle.normalize_pointed (c : ContinuousCocycle G N A)
    (a : A) (ha : ∀ g : G, c.toFun (1, g) = g • a - a) :
    (c.normalize a).Pointed := by
  intro g
  change c.toFun (1, g) - (g • a - a) = 0
  rw [ha, sub_self]

/-- Normalization preserves the class in `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem ContinuousCocycle.normalize_cohomologous (c : ContinuousCocycle G N A)
    (a : A) : c.Cohomologous (c.normalize a) := by
  refine ⟨-a, ?_⟩
  intro u g
  change c.toFun (u, g) - (g • a - a) = c.toFun (u, g) + (g • (-a) - (-a))
  rw [smul_neg]
  abel

/-- Independence of normalization choice in `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem ContinuousCocycle.normalize_unique (c : ContinuousCocycle G N A)
    (a b : A)
    (ha : ∀ g : G, c.toFun (1, g) = g • a - a)
    (hb : ∀ g : G, c.toFun (1, g) = g • b - b) :
    c.normalize a = c.normalize b := by
  apply ContinuousCocycle.ext
  rintro ⟨u, g⟩
  change c.toFun (u, g) - (g • a - a) = c.toFun (u, g) - (g • b - b)
  rw [← ha, ← hb]

/-- A continuous H¹ class trivial on the section has exactly one pointed cocycle.
Together with `pointedCocycleEquiv`, this proves the representative-level
formula of `K2-018#eq:k2018-pointed-character`, on the module source basis.
The additive H¹ structure and quotient-level `pointedH1AddEquiv` are constructed
below. The étale, mathlib-complex, and fundamental-group realizations remain
pending. -/
theorem ContinuousCocycle.pointedRepresentative_exists_unique
    (c : ContinuousCocycle G N A)
    (hsection : ∃ a : A, ∀ g : G, c.toFun (1, g) = g • a - a) :
    ∃! d : ContinuousCocycle G N A, d.Pointed ∧ c.Cohomologous d := by
  obtain ⟨a, ha⟩ := hsection
  refine ⟨c.normalize a, ⟨c.normalize_pointed a ha, c.normalize_cohomologous a⟩, ?_⟩
  intro d hd
  have hclass : (c.normalize a).Cohomologous d :=
    (c.normalize_cohomologous a).symm.trans hd.2
  exact ((pointed_cohomologous_iff_eq _ _ (c.normalize_pointed a ha) hd.1).mp hclass).symm

end Normalization

section Additive

variable [IsTopologicalAddGroup A]

/-- Auxiliary pointwise cocycle group for `K2-018#eq:k2018-pointed-character`,
using the module source basis. Continuity uses the topological coefficient group. -/
instance ContinuousCocycle.instZero : Zero (ContinuousCocycle G N A) := ⟨{
  toFun := fun _ => 0
  continuous_toFun := continuous_const
  cocycle := fun _ _ _ _ => by simp }⟩

/-- Auxiliary pointwise sum for `K2-018#eq:k2018-pointed-character`. -/
instance ContinuousCocycle.instAdd : Add (ContinuousCocycle G N A) := ⟨fun c d => {
  toFun := fun x => c.toFun x + d.toFun x
  continuous_toFun := c.continuous_toFun.add d.continuous_toFun
  cocycle := by intro u v g h; simp only [c.cocycle, d.cocycle, smul_add]; abel }⟩

/-- Auxiliary pointwise negative for `K2-018#eq:k2018-pointed-character`. -/
instance ContinuousCocycle.instNeg : Neg (ContinuousCocycle G N A) := ⟨fun c => {
  toFun := fun x => -c.toFun x
  continuous_toFun := c.continuous_toFun.neg
  cocycle := by intro u v g h; simp only [c.cocycle, smul_neg, neg_add] }⟩

/-- Auxiliary pointwise cocycle group for `K2-018#eq:k2018-pointed-character`. -/
instance ContinuousCocycle.instAddCommGroup : AddCommGroup (ContinuousCocycle G N A) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc c d e := by apply ContinuousCocycle.ext; intro x; exact add_assoc _ _ _
  zero_add c := by apply ContinuousCocycle.ext; intro x; exact zero_add _
  add_zero c := by apply ContinuousCocycle.ext; intro x; exact add_zero _
  neg_add_cancel c := by apply ContinuousCocycle.ext; intro x; exact neg_add_cancel _
  add_comm c d := by apply ContinuousCocycle.ext; intro x; exact add_comm _ _

/-- Auxiliary pointwise character group for `K2-018#eq:k2018-pointed-character`,
using the module source basis. -/
instance EquivariantCharacter.instZero : Zero (EquivariantCharacter G N A) := ⟨{
  toFun := fun _ => 0
  continuous_toFun := continuous_const
  map_mul := fun _ _ => by simp
  map_action := fun _ _ => by simp }⟩

/-- Auxiliary pointwise sum for `K2-018#eq:k2018-pointed-character`. -/
instance EquivariantCharacter.instAdd : Add (EquivariantCharacter G N A) := ⟨fun f k => {
  toFun := fun u => f.toFun u + k.toFun u
  continuous_toFun := f.continuous_toFun.add k.continuous_toFun
  map_mul := by intro u v; simp only [f.map_mul, k.map_mul]; abel
  map_action := by intro g u; simp only [f.map_action, k.map_action, smul_add] }⟩

/-- Auxiliary pointwise negative for `K2-018#eq:k2018-pointed-character`. -/
instance EquivariantCharacter.instNeg : Neg (EquivariantCharacter G N A) := ⟨fun f => {
  toFun := fun u => -f.toFun u
  continuous_toFun := f.continuous_toFun.neg
  map_mul := by intro u v; simp only [f.map_mul, neg_add]
  map_action := by intro g u; simp only [f.map_action, smul_neg] }⟩

/-- Auxiliary pointwise character group for `K2-018#eq:k2018-pointed-character`. -/
instance EquivariantCharacter.instAddCommGroup : AddCommGroup (EquivariantCharacter G N A) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f k l := by apply EquivariantCharacter.ext; intro u; exact add_assoc _ _ _
  zero_add f := by apply EquivariantCharacter.ext; intro u; exact zero_add _
  add_zero f := by apply EquivariantCharacter.ext; intro u; exact add_zero _
  neg_add_cancel f := by apply EquivariantCharacter.ext; intro u; exact neg_add_cancel _
  add_comm f k := by apply EquivariantCharacter.ext; intro u; exact add_comm _ _

omit [IsTopologicalAddGroup A] in
/-- Auxiliary pointwise evaluation rule for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem ContinuousCocycle.zero_toFun (x : N × G) :
    (0 : ContinuousCocycle G N A).toFun x = 0 := rfl

/-- Auxiliary pointwise evaluation rule for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem ContinuousCocycle.add_toFun (c d : ContinuousCocycle G N A) (x : N × G) :
    (c + d).toFun x = c.toFun x + d.toFun x := rfl

/-- Auxiliary pointwise evaluation rule for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem ContinuousCocycle.neg_toFun (c : ContinuousCocycle G N A) (x : N × G) :
    (-c).toFun x = -c.toFun x := rfl

/-- Auxiliary pointwise evaluation rule for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem ContinuousCocycle.sub_toFun (c d : ContinuousCocycle G N A) (x : N × G) :
    (c - d).toFun x = c.toFun x - d.toFun x := by
  simp [sub_eq_add_neg]

omit [TopologicalSpace G] in
/-- Auxiliary pointwise evaluation rule for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem EquivariantCharacter.add_toFun (f k : EquivariantCharacter G N A) (u : N) :
    (f + k).toFun u = f.toFun u + k.toFun u := rfl

variable [ContinuousSMul G A]

/-- Auxiliary continuous coboundary homomorphism for
`K2-018#eq:k2018-pointed-character`, using the module source basis. -/
def coboundaryHom : A →+ ContinuousCocycle G N A where
  toFun a := {
    toFun := fun x => x.2 • a - a
    continuous_toFun := (continuous_snd.smul continuous_const).sub continuous_const
    cocycle := by intro u v g h; simp only [mul_smul, smul_sub]; abel }
  map_zero' := by apply ContinuousCocycle.ext; intro x; simp
  map_add' a b := by
    apply ContinuousCocycle.ext
    intro x
    change x.2 • (a + b) - (a + b) = (x.2 • a - a) + (x.2 • b - b)
    rw [smul_add]
    abel

/-- Auxiliary coboundary subgroup for `K2-018#eq:k2018-pointed-character`,
using the module source basis. -/
def coboundaries : AddSubgroup (ContinuousCocycle G N A) :=
  (coboundaryHom (G := G) (N := N) (A := A)).range

/-- Auxiliary comparison of the accepted cocycle relation with the additive
coboundary subgroup for `K2-018#eq:k2018-pointed-character`. -/
theorem cohomologous_iff_sub_mem (c d : ContinuousCocycle G N A) :
    c.Cohomologous d ↔ d - c ∈ coboundaries (G := G) (N := N) (A := A) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply ContinuousCocycle.ext
    rintro ⟨u, g⟩
    rw [ContinuousCocycle.sub_toFun]
    change g • a - a = d.toFun (u, g) - c.toFun (u, g)
    rw [ha]
    abel
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro u g
    have h := congrArg (fun z : ContinuousCocycle G N A => z.toFun (u, g)) ha
    rw [ContinuousCocycle.sub_toFun] at h
    change g • a - a = d.toFun (u, g) - c.toFun (u, g) at h
    rw [h]
    abel

/-- A separate type synonym prevents Lean from selecting the ordinary product
group when forming the common cohomology quotient. -/
def CoordinateGroup (G N : Type*) := N × G

instance coordinateTopology : TopologicalSpace (CoordinateGroup G N) :=
  inferInstanceAs (TopologicalSpace (N × G))

/-- The split-coordinate group has semidirect multiplication; the ordinary
product group is never used for the common cohomology specialization. -/
instance coordinateGroup : Group (CoordinateGroup G N) where
  mul x y := (x.1 * x.2 • y.1, x.2 * y.2)
  one := (1, 1)
  inv x := (x.2⁻¹ • x.1⁻¹, x.2⁻¹)
  div x y := (x.1 * x.2 • (y.2⁻¹ • y.1⁻¹), x.2 * y.2⁻¹)
  npow := @npowRec (CoordinateGroup G N) ⟨(1, 1)⟩ ⟨fun x y => (x.1 * x.2 • y.1, x.2 * y.2)⟩
  zpow := @zpowRec (CoordinateGroup G N) ⟨(1, 1)⟩ ⟨fun x y => (x.1 * x.2 • y.1, x.2 * y.2)⟩
    ⟨fun x => (x.2⁻¹ • x.1⁻¹, x.2⁻¹)⟩
    (@npowRec (CoordinateGroup G N) ⟨(1, 1)⟩ ⟨fun x y => (x.1 * x.2 • y.1, x.2 * y.2)⟩)
  mul_assoc x y z := by
    apply Prod.ext
    · change (x.1 * x.2 • y.1) * (x.2 * y.2) • z.1 =
        x.1 * x.2 • (y.1 * y.2 • z.1)
      simp [mul_smul, smul_mul', mul_assoc]
    · exact mul_assoc _ _ _
  one_mul x := by
    apply Prod.ext
    · change 1 * (1 : G) • x.1 = x.1
      simp
    · exact one_mul _
  mul_one x := by
    apply Prod.ext
    · change x.1 * x.2 • (1 : N) = x.1
      simp
    · exact mul_one _
  inv_mul_cancel x := by
    apply Prod.ext
    · change (x.2⁻¹ • x.1⁻¹) * x.2⁻¹ • x.1 = 1
      rw [← smul_mul']
      simp
    · exact inv_mul_cancel _

/-- Inflated coefficients: only the arithmetic coordinate acts. -/
instance coordinateAction : DistribMulAction (CoordinateGroup G N) A where
  smul x a := x.2 • a
  one_smul a := one_smul G a
  mul_smul x y a := mul_smul x.2 y.2 a
  smul_zero x := smul_zero x.2
  smul_add x a b := smul_add x.2 a b

instance coordinateContinuousSMul : ContinuousSMul (CoordinateGroup G N) A :=
  ⟨(continuous_snd.comp continuous_fst).smul continuous_snd⟩

/-- Continuous H¹ of the split extension is the common continuous-cochain
quotient for its actual semidirect group and inflated coefficient action.
Its additive structure is the common quotient's structure. -/
abbrev ContinuousH1 := GroupCohomology.ContinuousH1.H1 (CoordinateGroup G N) A

/-- The working coordinate record is exactly a cocycle of the semidirect group.
This internal conversion introduces no second cohomology quotient. -/
def coordinateCocycleEquiv : ContinuousCocycle G N A ≃+
    GroupCohomology.ContinuousH1.Cocycle (CoordinateGroup G N) A where
  toFun c := ⟨⟨c.toFun, c.continuous_toFun⟩, by
    rintro ⟨u, g⟩ ⟨v, h⟩
    exact c.cocycle u v g h⟩
  invFun c := {
    toFun := c.val
    continuous_toFun := c.continuous
    cocycle := fun u v g h => c.map_mul (u, g) (v, h) }
  left_inv c := by apply ContinuousCocycle.ext; intro x; rfl
  right_inv c := by apply GroupCohomology.ContinuousH1.Cocycle.ext; intro x; rfl
  map_add' c d := by apply GroupCohomology.ContinuousH1.Cocycle.ext; intro x; rfl

private theorem coordinateCocycleEquiv_coboundary (a : A) :
    coordinateCocycleEquiv (coboundaryHom (G := G) (N := N) a) =
      GroupCohomology.ContinuousH1.principal (CoordinateGroup G N) A a := by
  apply GroupCohomology.ContinuousH1.Cocycle.ext
  intro x
  rfl

/-- Projection from coordinate cocycles to the one common continuous H¹ quotient,
for `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def continuousH1Mk : ContinuousCocycle G N A →+
    ContinuousH1 (G := G) (N := N) (A := A) :=
  (GroupCohomology.ContinuousH1.classOf (CoordinateGroup G N) A).comp
    coordinateCocycleEquiv.toAddMonoidHom

/-- The coordinate class constructor is the class constructor of the common
continuous H¹ quotient, for `K2-018#eq:k2018-pointed-character`. -/
@[simp] theorem continuousH1Mk_eq (c : ContinuousCocycle G N A) :
    continuousH1Mk c = GroupCohomology.ContinuousH1.classOf (CoordinateGroup G N) A
      (coordinateCocycleEquiv c) := rfl

/-- Every class in the common quotient has a coordinate cocycle representative. -/
theorem continuousH1Mk_surjective : Function.Surjective
    (continuousH1Mk (G := G) (N := N) (A := A)) :=
  (GroupCohomology.ContinuousH1.classOf_surjective (CoordinateGroup G N) A).comp
    coordinateCocycleEquiv.surjective

/-- Equality in the common continuous H¹ quotient is precisely the original
coordinate coboundary relation of `K2-018#eq:k2018-pointed-character`. -/
theorem continuousH1Mk_eq_iff (c d : ContinuousCocycle G N A) :
    continuousH1Mk c = continuousH1Mk d ↔ c.Cohomologous d := by
  change GroupCohomology.ContinuousH1.classOf (CoordinateGroup G N) A (coordinateCocycleEquiv c) =
    GroupCohomology.ContinuousH1.classOf (CoordinateGroup G N) A (coordinateCocycleEquiv d) ↔ _
  rw [GroupCohomology.ContinuousH1.classOf_eq_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    intro u g
    have h := congrArg (fun z : GroupCohomology.ContinuousH1.Cocycle (CoordinateGroup G N) A =>
      z.val (u, g)) ha
    change g • a - a = c.toFun (u, g) - d.toFun (u, g) at h
    calc
      d.toFun (u, g) = c.toFun (u, g) - (c.toFun (u, g) - d.toFun (u, g)) := by abel
      _ = c.toFun (u, g) - (g • a - a) := by rw [← h]
      _ = c.toFun (u, g) + (g • (-a) - (-a)) := by rw [smul_neg]; abel
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    apply GroupCohomology.ContinuousH1.Cocycle.ext
    rintro ⟨u, g⟩
    change g • (-a) - (-a) = c.toFun (u, g) - d.toFun (u, g)
    rw [ha, smul_neg]
    abel

/-- The zero class consists of continuous coboundaries for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem continuousH1Mk_eq_zero_iff (c : ContinuousCocycle G N A) :
    continuousH1Mk c = 0 ↔
      ∃ a : A, ∀ u : N, ∀ g : G, c.toFun (u, g) = g • a - a := by
  have hzero : continuousH1Mk (0 : ContinuousCocycle G N A) = 0 := map_zero _
  rw [← hzero, eq_comm, continuousH1Mk_eq_iff]
  simp [ContinuousCocycle.Cohomologous]

/-- The coordinate universal property is derived directly from the common
continuous H¹ quotient, for `K2-018#eq:k2018-pointed-character`. -/
def continuousH1Lift {B : Type*} [AddCommGroup B]
    (f : ContinuousCocycle G N A →+ B)
    (hf : coboundaries (G := G) (N := N) (A := A) ≤ f.ker) :
    ContinuousH1 (G := G) (N := N) (A := A) →+ B :=
  QuotientAddGroup.lift (GroupCohomology.ContinuousH1.coboundaries (CoordinateGroup G N) A)
    (f.comp coordinateCocycleEquiv.symm.toAddMonoidHom) (by
      rintro c ⟨a, rfl⟩
      change f (coordinateCocycleEquiv.symm
        (GroupCohomology.ContinuousH1.principal (CoordinateGroup G N) A a)) = 0
      rw [← coordinateCocycleEquiv_coboundary, AddEquiv.symm_apply_apply]
      exact hf ⟨a, rfl⟩)

/-- Auxiliary representative formula for the H¹ universal property in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem continuousH1Lift_mk {B : Type*} [AddCommGroup B]
    (f : ContinuousCocycle G N A →+ B)
    (hf : coboundaries (G := G) (N := N) (A := A) ≤ f.ker)
    (c : ContinuousCocycle G N A) : continuousH1Lift f hf (continuousH1Mk c) = f c := rfl

/-- Auxiliary trivial geometric action for the section-cohomology model in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
instance sectionGeometricAction : MulDistribMulAction G PUnit.{1} where
  smul _ _ := PUnit.unit
  one_smul _ := Subsingleton.elim _ _
  mul_smul _ _ _ := Subsingleton.elim _ _
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- The chosen-section restriction on continuous cocycles for
`K2-018#eq:k2018-pointed-character`, using the trivial geometric group model. -/
def sectionCocycleHom : ContinuousCocycle G N A →+ ContinuousCocycle G PUnit.{1} A where
  toFun c := {
    toFun x := c.toFun (1, x.2)
    continuous_toFun := c.continuous_toFun.comp (continuous_const.prodMk continuous_snd)
    cocycle := by intro u v g h; simpa using c.cocycle 1 1 g h }
  map_zero' := by apply ContinuousCocycle.ext; intro x; rfl
  map_add' c d := by apply ContinuousCocycle.ext; intro x; rfl

/-- Section restriction preserves the same coefficient coboundary in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem sectionCocycleHom_coboundary (a : A) :
    sectionCocycleHom (coboundaryHom (G := G) (N := N) a) =
      coboundaryHom (G := G) (N := PUnit.{1}) a := by
  apply ContinuousCocycle.ext
  intro x
  rfl

/-- Genuine additive restriction to the section's continuous H¹ for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def continuousH1SectionRestriction :
    ContinuousH1 (G := G) (N := N) (A := A) →+
      ContinuousH1 (G := G) (N := PUnit.{1}) (A := A) :=
  continuousH1Lift
    ((continuousH1Mk (G := G) (N := PUnit.{1}) (A := A)).comp sectionCocycleHom) (by
      rintro c ⟨a, rfl⟩
      change continuousH1Mk (sectionCocycleHom (coboundaryHom (G := G) (N := N) a)) = 0
      rw [sectionCocycleHom_coboundary]
      apply (continuousH1Mk_eq_zero_iff _).mpr
      exact ⟨a, fun _ _ => rfl⟩)

/-- Auxiliary class formula for section restriction in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem continuousH1SectionRestriction_mk (c : ContinuousCocycle G N A) :
    continuousH1SectionRestriction (continuousH1Mk c) =
      continuousH1Mk (sectionCocycleHom c) := rfl

/-- Pointed continuous H¹ is the kernel of actual section restriction, as in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def PointedH1 : AddSubgroup (ContinuousH1 (G := G) (N := N) (A := A)) :=
  (continuousH1SectionRestriction (G := G) (N := N) (A := A)).ker

/-- Representative criterion for the pointed continuous H¹ kernel in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem continuousH1Mk_mem_pointed_iff (c : ContinuousCocycle G N A) :
    continuousH1Mk c ∈ PointedH1 (G := G) (N := N) (A := A) ↔
      ∃ a : A, ∀ g : G, c.toFun (1, g) = g • a - a := by
  rw [PointedH1, AddMonoidHom.mem_ker, continuousH1SectionRestriction_mk,
    continuousH1Mk_eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun g => ha PUnit.unit g⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun _ g => ha g⟩

omit [IsTopologicalAddGroup A] [ContinuousSMul G A] in
/-- Auxiliary split-coordinate decomposition of any continuous cocycle for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem ContinuousCocycle.value_decomposition (c : ContinuousCocycle G N A)
    (u : N) (g : G) : c.toFun (u, g) = c.toFun (u, 1) + c.toFun (1, g) := by
  simpa using c.cocycle u 1 1 g

/-- Geometric restriction of any cocycle is a continuous equivariant character
in `K2-018#eq:k2018-pointed-character`, on the module source basis. Commutativity
of the coefficients cancels the section term without first normalizing. -/
def geometricCocycleHom : ContinuousCocycle G N A →+ EquivariantCharacter G N A where
  toFun c := {
    toFun u := c.toFun (u, 1)
    continuous_toFun := c.continuous_toFun.comp (continuous_id.prodMk continuous_const)
    map_mul := by intro u v; simpa using c.cocycle u v 1 1
    map_action := by
      intro g u
      apply add_right_cancel (b := c.toFun (1, g))
      calc
        c.toFun (g • u, 1) + c.toFun (1, g) = c.toFun (g • u, g) :=
          (c.value_decomposition (g • u) g).symm
        _ = g • c.toFun (u, 1) + c.toFun (1, g) := by
          simpa [add_comm] using c.cocycle 1 u g 1 }
  map_zero' := by apply EquivariantCharacter.ext; intro u; rfl
  map_add' c d := by apply EquivariantCharacter.ext; intro u; rfl

/-- Geometric restriction kills coboundaries in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem geometricCocycleHom_coboundary (a : A) :
    geometricCocycleHom (coboundaryHom (G := G) (N := N) a) = 0 := by
  apply EquivariantCharacter.ext
  intro u
  change (1 : G) • a - a = 0
  simp

/-- Geometric restriction descends to genuine additive continuous H¹ in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def geometricH1Hom : ContinuousH1 (G := G) (N := N) (A := A) →+
    EquivariantCharacter G N A :=
  continuousH1Lift (geometricCocycleHom (G := G) (N := N) (A := A)) (by
    rintro c ⟨a, rfl⟩
    exact geometricCocycleHom_coboundary a)

/-- Auxiliary representative formula for geometric H¹ restriction in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem geometricH1Hom_mk (c : ContinuousCocycle G N A) :
    geometricH1Hom (continuousH1Mk c) = geometricCocycleHom c := rfl

/-- Character extension defines an additive cocycle map for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def characterExtensionHom : EquivariantCharacter G N A →+ ContinuousCocycle G N A where
  toFun := EquivariantCharacter.extend
  map_zero' := by apply ContinuousCocycle.ext; intro x; rfl
  map_add' f k := by apply ContinuousCocycle.ext; intro x; rfl

/-- The extension class is pointed in `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem characterExtension_pointed (f : EquivariantCharacter G N A) :
    continuousH1Mk f.extend ∈ PointedH1 (G := G) (N := N) (A := A) := by
  apply (continuousH1Mk_mem_pointed_iff _).mpr
  exact ⟨0, fun g => by simpa using f.extend_pointed g⟩

/-- A section-trivial class equals the extension of its geometric character
in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem geometric_extension_class_eq (c : ContinuousCocycle G N A)
    (hc : continuousH1Mk c ∈ PointedH1 (G := G) (N := N) (A := A)) :
    continuousH1Mk (geometricCocycleHom c).extend = continuousH1Mk c := by
  obtain ⟨a, ha⟩ := (continuousH1Mk_mem_pointed_iff c).mp hc
  apply (continuousH1Mk_eq_iff _ _).mpr
  apply ContinuousCocycle.Cohomologous.symm
  refine ⟨-a, ?_⟩
  intro u g
  change c.toFun (u, 1) = c.toFun (u, g) + (g • (-a) - (-a))
  rw [c.value_decomposition u g, ha g, smul_neg]
  abel

/-- The additive pointed continuous H¹ formula of
`K2-018#eq:k2018-pointed-character`, on the module source basis. The section
restriction is genuine cohomology restriction; étale and fundamental-group
realizations remain separate obligations. The inverse is the extension class. -/
def pointedH1AddEquiv : PointedH1 (G := G) (N := N) (A := A) ≃+
    EquivariantCharacter G N A where
  toFun q := geometricH1Hom q.1
  invFun f := ⟨continuousH1Mk f.extend, characterExtension_pointed f⟩
  left_inv q := by
    apply Subtype.ext
    obtain ⟨c, hc⟩ := continuousH1Mk_surjective q.1
    have hpointed : continuousH1Mk c ∈ PointedH1 (G := G) (N := N) (A := A) := by
      rw [hc]
      exact q.2
    change continuousH1Mk (geometricH1Hom q.1).extend = q.1
    rw [← hc, geometricH1Hom_mk]
    exact geometric_extension_class_eq c hpointed
  right_inv f := by
    change geometricH1Hom (continuousH1Mk f.extend) = f
    rw [geometricH1Hom_mk]
    apply EquivariantCharacter.ext
    intro u
    rfl
  map_add' q r := (geometricH1Hom (G := G) (N := N) (A := A)).map_add q.1 r.1

/-- Explicit inverse formula for pointed continuous H¹ in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem pointedH1AddEquiv_symm_apply (f : EquivariantCharacter G N A) :
    ((pointedH1AddEquiv (G := G) (N := N) (A := A)).symm f).1 =
      continuousH1Mk f.extend := rfl

end Additive

end GroupCohomology.PointedCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c454062603b592583f687feafd181ddcc3b344acfde920eb0563fbb7ce301e80.
Definitions, hypotheses and universes are retained modulo native names. -/
