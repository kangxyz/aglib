/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H2.Continuous
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Tactic.Group

/-!
# Coset sections and continuous finite-open transfer

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestriction.lean`.
SHA-256: `479e6eeeb40e0da2f9def4a40653e65cb8d5fe17062a5420175c1384ba90eca7`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestrictionTower.lean`.
SHA-256: `4efbe8f9c2b98cb390b8f9477e3ad04f3dcdf34cc6baa90240af30a980e5aebe`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.Continuous.Corestriction
variable (G : Type*) [_root_.Group G] (H : Subgroup G)

def shift (g : G) (x : G ⧸ H) : G ⧸ H := g⁻¹ • x

theorem shift_mul (g h : G) (x : G ⧸ H) :
    shift G H (g * h) x = shift G H h (shift G H g x) := by
  simp only [shift, mul_inv_rev, mul_smul]

def representative (x : G ⧸ H) : G := x.out

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_shift : Continuous (fun p : G × (G ⧸ H) => shift G H p.1 p.2) :=
  continuous_fst.inv.smul continuous_snd

variable (A : Type*) [AddCommGroup A] [H.FiniteIndex]
local instance : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sum_shift (g : G) (f : G ⧸ H → A) :
    ∑ x : G ⧸ H, f (shift G H g x) = ∑ x : G ⧸ H, f x :=
  Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun _ => rfl)

end GroupCohomology.Continuous.Corestriction

namespace GroupCohomology.Continuous.Corestriction
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)

/-- An actual section of the quotient by a subgroup. -/
structure CosetSection (G : Type*) [_root_.Group G] (H : Subgroup G) where
  rep : G ⧸ H → G
  proj : ∀ x, QuotientGroup.mk (rep x) = x

namespace CosetSection
variable {G : Type*} [_root_.Group G] {H : Subgroup G}
variable (r : CosetSection G H)

/-- The original frozen section, using the quotient's chosen representative. -/
def chosen : CosetSection G H := ⟨representative G H, QuotientGroup.out_eq'⟩

theorem factor_mem (g : G) (x : G ⧸ H) :
    (r.rep x)⁻¹ * g * r.rep (shift G H g x) ∈ H := by
  rw [mul_assoc]
  apply QuotientGroup.eq.mp
  change QuotientGroup.mk (r.rep x) = QuotientGroup.mk (g * r.rep (shift G H g x))
  change QuotientGroup.mk (r.rep x) = g • (QuotientGroup.mk (r.rep (shift G H g x)) : G ⧸ H)
  rw [r.proj, r.proj]
  exact (smul_inv_smul g x).symm

def factor (g : G) (x : G ⧸ H) : H :=
  ⟨(r.rep x)⁻¹ * g * r.rep (shift G H g x), factor_mem r g x⟩

theorem factor_mul (g h : G) (x : G ⧸ H) :
    factor r (g * h) x = factor r g x * factor r h (shift G H g x) := by
  apply Subtype.ext
  change (r.rep x)⁻¹ * (g * h) * r.rep (shift G H (g * h) x) =
    ((r.rep x)⁻¹ * g * r.rep (shift G H g x)) *
      ((r.rep (shift G H g x))⁻¹ * h * r.rep (shift G H h (shift G H g x)))
  rw [shift_mul]
  group

theorem representative_factor (g : G) (x : G ⧸ H) :
    r.rep x * (factor r g x : G) = g * r.rep (shift G H g x) := by
  change r.rep x * ((r.rep x)⁻¹ * g * r.rep (shift G H g x)) = _
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (hH : IsOpen (H : Set G))

include hH in
theorem continuous_rep : Continuous r.rep := by
  let := QuotientGroup.discreteTopology hH
  exact continuous_of_discreteTopology

include hH in
theorem continuous_factor : Continuous (fun p : G × (G ⧸ H) => factor r p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (((continuous_rep r hH).comp continuous_snd).inv.mul continuous_fst).mul
    ((continuous_rep r hH).comp (continuous_shift G H))


variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable [H.FiniteIndex]
local instance : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] [H.FiniteIndex] in
theorem representative_factor_smul (g : G) (x : G ⧸ H) (a : A) :
    r.rep x • (factor r g x • a) =
      g • (r.rep (shift G H g x) • a) := by
  change r.rep x • ((factor r g x : G) • a) = _
  rw [← mul_smul, representative_factor, mul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] in
theorem sum_factor_smul (g : G) (f : G ⧸ H → A) :
    ∑ x : G ⧸ H, r.rep x • (factor r g x • f (shift G H g x)) =
      g • ∑ x : G ⧸ H, r.rep x • f x := by
  simp only [representative_factor_smul, ← Finset.smul_sum]
  exact congrArg (g • ·) (sum_shift G H A g (fun x => r.rep x • f x))

/-- The actual degree-zero transfer cochain. -/
def transfer₀ : A →+ A where
  toFun a := ∑ x : G ⧸ H, r.rep x • a
  map_zero' := by simp
  map_add' a b := by simp [smul_add, Finset.sum_add_distrib]

/-- The actual continuous degree-one cochain transfer. -/
def transfer₁ : C(H, A) →+ C(G, A) where
  toFun b := ⟨fun g => ∑ x : G ⧸ H, r.rep x • b (factor r g x), by
    apply continuous_finsetSum
    intro x hx
    exact continuous_const.smul (b.continuous.comp
      ((continuous_factor r hH).comp (continuous_id.prodMk continuous_const)))⟩
  map_zero' := by ext g; simp
  map_add' b c := by ext g; simp [smul_add, Finset.sum_add_distrib]

@[simp] theorem transfer₁_apply (b : C(H, A)) (g : G) :
    transfer₁ r hH A b g =
      ∑ x : G ⧸ H, r.rep x • b (factor r g x) := rfl

/-- The actual continuous degree-two cochain transfer. -/
def transfer₂ : C(H × H, A) →+ C(G × G, A) where
  toFun c := ⟨fun p => ∑ x : G ⧸ H, r.rep x •
      c (factor r p.1 x, factor r p.2 (shift G H p.1 x)), by
    apply continuous_finsetSum
    intro x hx
    exact continuous_const.smul (c.continuous.comp
      (((continuous_factor r hH).comp (continuous_fst.prodMk continuous_const)).prodMk
        ((continuous_factor r hH).comp
          (continuous_snd.prodMk
            ((continuous_shift G H).comp (continuous_fst.prodMk continuous_const))))))⟩
  map_zero' := by ext p; simp
  map_add' b c := by ext p; simp [smul_add, Finset.sum_add_distrib]

@[simp] theorem transfer₂_apply (c : C(H × H, A)) (g h : G) :
    transfer₂ r hH A c (g, h) =
      ∑ x : G ⧸ H, r.rep x •
        c (factor r g x, factor r h (shift G H g x)) := rfl

/-- Transfer takes genuine continuous two-cocycles to genuine two-cocycles. -/
theorem transfer₂_cocycle (c : Cocycle H A) (g h k : G) :
    transfer₂ r hH A c.val (g, h) + transfer₂ r hH A c.val (g * h, k) =
      g • transfer₂ r hH A c.val (h, k) + transfer₂ r hH A c.val (g, h * k) := by
  simp only [transfer₂_apply, ← Finset.sum_add_distrib, ← smul_add, factor_mul, shift_mul]
  have hp : ∀ x : G ⧸ H,
      c.val (factor r g x, factor r h (shift G H g x)) +
        c.val (factor r g x * factor r h (shift G H g x),
          factor r k (shift G H h (shift G H g x))) =
      factor r g x • c.val (factor r h (shift G H g x),
        factor r k (shift G H h (shift G H g x))) +
        c.val (factor r g x,
          factor r h (shift G H g x) * factor r k (shift G H h (shift G H g x))) :=
    fun x => c.property _ _ _
  simp_rw [hp, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact sum_factor_smul r A g (fun x =>
    c.val (factor r h x, factor r k (shift G H h x)))

/-- Transfer restricted to genuine continuous two-cocycles. -/
def transferCocycles₂ : Cocycle H A →+ Cocycle G A where
  toFun c := ⟨transfer₂ r hH A c.val, transfer₂_cocycle r hH A c⟩
  map_zero' := Subtype.ext (map_zero (transfer₂ r hH A))
  map_add' c d := Subtype.ext (map_add (transfer₂ r hH A) c.val d.val)

/-- The cochain transfer commutes with the genuine bar differential. -/
theorem transfer_d₁ (b : C(H, A)) :
    transferCocycles₂ r hH A (d₁ H A b) = d₁ G A (transfer₁ r hH A b) := by
  apply Cocycle.ext
  intro g h
  change (∑ x : G ⧸ H, r.rep x •
    ((factor r g x) • b (factor r h (shift G H g x)) -
      b (factor r g x * factor r h (shift G H g x)) + b (factor r g x))) =
    g • (∑ x : G ⧸ H, r.rep x • b (factor r h x)) -
      (∑ x : G ⧸ H, r.rep x • b (factor r (g * h) x)) +
      (∑ x : G ⧸ H, r.rep x • b (factor r g x))
  simp_rw [← factor_mul, smul_add, smul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_factor_smul r A g (fun x => b (factor r h x))]

/-- The constructed transfer also preserves continuous one-cocycles. -/
def transferCocycles₁ : ContinuousH1.Cocycle H A →+ ContinuousH1.Cocycle G A where
  toFun c := ⟨transfer₁ r hH A c.val, by
    apply (d₁_eq_zero_iff G A _).mp
    rw [← transfer_d₁, d₁_cocycle, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (transfer₁ r hH A))
  map_add' c d := Subtype.ext (map_add (transfer₁ r hH A) c.val d.val)

/-- The same formula transfers principal cocycles to principal cocycles. -/
theorem transfer_principal (a : A) :
    transferCocycles₁ r hH A (ContinuousH1.principal H A a) =
      ContinuousH1.principal G A (transfer₀ r A a) := by
  apply ContinuousH1.Cocycle.ext
  intro g
  change (∑ x : G ⧸ H, r.rep x • (factor r g x • a - a)) =
    g • (∑ x : G ⧸ H, r.rep x • a) -
      (∑ x : G ⧸ H, r.rep x • a)
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact sum_factor_smul r A g (fun _ => a)

/-- The induced native continuous H1 corestriction. -/
def corestriction₁ : ContinuousH1.H1 H A →+ ContinuousH1.H1 G A :=
  QuotientAddGroup.map _ _ (transferCocycles₁ r hH A) (by
    rintro c ⟨a, rfl⟩
    exact ⟨transfer₀ r A a, (transfer_principal r hH A a).symm⟩)

@[simp] theorem corestriction₁_class (c : ContinuousH1.Cocycle H A) :
    corestriction₁ r hH A (ContinuousH1.classOf H A c) =
      ContinuousH1.classOf G A (transferCocycles₁ r hH A c) := rfl

/-- Transfer on the existing smart-truncation cycle subtype. -/
def transferCycles₂ : (complex H A).Cycles₂ →+ (complex G A).Cycles₂ where
  toFun c := ⟨transferCocycles₂ r hH A c.val, rfl⟩
  map_zero' := Subtype.ext (map_zero (transferCocycles₂ r hH A))
  map_add' c d := Subtype.ext (map_add (transferCocycles₂ r hH A) c.val d.val)

/-- The actual boundary subgroup is preserved by the constructed cochain map. -/
theorem transfer_boundary₂ (b : C(H, A)) :
    transferCycles₂ r hH A ((complex H A).boundary₂ b) =
      (complex G A).boundary₂ (transfer₁ r hH A b) :=
  Subtype.ext (transfer_d₁ r hH A b)

/-- Native continuous H2 corestriction, constructed on its actual quotient. -/
def corestriction₂ : H2.Continuous.Group H A →+ H2.Continuous.Group G A :=
  QuotientAddGroup.map _ _ (transferCycles₂ r hH A) (by
    rintro c ⟨b, rfl⟩
    exact ⟨transfer₁ r hH A b, (transfer_boundary₂ r hH A b).symm⟩)

@[simp] theorem corestriction₂_class (c : Cocycle H A) :
    corestriction₂ r hH A (classOf H A c) =
      classOf G A (transferCocycles₂ r hH A c) := rfl




end CosetSection
end GroupCohomology.Continuous.Corestriction
