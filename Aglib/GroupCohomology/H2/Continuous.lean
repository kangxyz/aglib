/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous
public import Aglib.Algebra.Homology.MultiplicationCone

/-!
# Continuous two-cocycles and their actual H2 quotient

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousLowDegree.lean`.
SHA-256: `04751c3c4a190315f993e330e8bc90b23d1fb50b731bc0bce06cf3d1a452891a`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.H2.Continuous

variable (G A : Type*) [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- Actual continuous inhomogeneous two-cocycles. -/
def cocycles : AddSubgroup C(G × G, A) where
  carrier := {z | ∀ g h k : G,
    z (g, h) + z (g * h, k) = g • z (h, k) + z (g, h * k)}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw g h k
    simp only [ContinuousMap.add_apply, smul_add]
    rw [show z (g, h) + w (g, h) + (z (g * h, k) + w (g * h, k)) =
      (z (g, h) + z (g * h, k)) + (w (g, h) + w (g * h, k)) by abel]
    rw [hz, hw]
    abel
  neg_mem' := by
    intro z hz g h k
    simpa only [ContinuousMap.neg_apply, smul_neg, ← neg_add] using
      congrArg Neg.neg (hz g h k)

abbrev Cocycle := cocycles G A

omit [IsTopologicalGroup G] [ContinuousSMul G A] in
@[ext] theorem Cocycle.ext {z w : Cocycle G A}
    (h : ∀ g k, z.val (g, k) = w.val (g, k)) : z = w := by
  apply Subtype.ext
  ext p
  exact h p.1 p.2

/-- The actual degree-zero differential, with the existing H¹ sign convention. -/
def d₀ : A →+ C(G, A) :=
  (ContinuousH1.cocycles G A).subtype.comp (ContinuousH1.principal G A)

omit [IsTopologicalGroup G] in
@[simp] theorem d₀_apply (a : A) (g : G) : d₀ G A a g = g • a - a := rfl

/-- The bar differential lands in genuine two-cocycles. -/
def d₁ : C(G, A) →+ Cocycle G A where
  toFun a := ⟨⟨fun p => p.1 • a p.2 - a (p.1 * p.2) + a p.1,
    ((continuous_fst.smul (a.continuous.comp continuous_snd)).sub
      (a.continuous.comp (continuous_fst.mul continuous_snd))).add
      (a.continuous.comp continuous_fst)⟩, by
    intro g h k
    change (g • a h - a (g * h) + a g) +
      ((g * h) • a k - a ((g * h) * k) + a (g * h)) =
      g • (h • a k - a (h * k) + a h) +
      (g • a (h * k) - a (g * (h * k)) + a g)
    simp only [mul_smul, smul_add, smul_sub, mul_assoc]
    abel⟩
  map_zero' := by apply Cocycle.ext; intro g h; simp
  map_add' a b := by
    apply Cocycle.ext
    intro g h
    change g • (a h + b h) - (a (g * h) + b (g * h)) + (a g + b g) =
      (g • a h - a (g * h) + a g) + (g • b h - b (g * h) + b g)
    rw [smul_add]
    abel

@[simp] theorem d₁_apply (a : C(G, A)) (g h : G) :
    (d₁ G A a).val (g, h) = g • a h - a (g * h) + a g := rfl

theorem d₁_d₀ (a : A) : d₁ G A (d₀ G A a) = 0 := by
  apply Cocycle.ext
  intro g h
  change g • (h • a - a) - ((g * h) • a - a) + (g • a - a) = 0
  simp only [smul_sub, mul_smul]
  abel

theorem d₁_eq_zero_iff (a : C(G, A)) :
    d₁ G A a = 0 ↔ ∀ g h : G, a (g * h) = a g + g • a h := by
  constructor
  · intro ha g h
    have hp := congrArg (fun b : Cocycle G A => b.val (g, h)) ha
    change g • a h - a (g * h) + a g = 0 at hp
    have he : a g + g • a h - a (g * h) = 0 := by
      calc
        _ = g • a h - a (g * h) + a g := by abel
        _ = 0 := hp
    exact (sub_eq_zero.mp he).symm
  · intro ha
    apply Cocycle.ext
    intro g h
    change g • a h - a (g * h) + a g = 0
    rw [ha]
    abel

def cocycle₁OfClosed (a : C(G, A)) (ha : d₁ G A a = 0) : ContinuousH1.Cocycle G A :=
  ⟨a, (d₁_eq_zero_iff G A a).mp ha⟩

theorem d₁_cocycle (c : ContinuousH1.Cocycle G A) : d₁ G A c.val = 0 :=
  (d₁_eq_zero_iff G A c.val).mpr c.property

/-- Smart truncation of the continuous bar complex: the second term is Z². -/
def complex : AddCommGrpCat.MultiplicationCone.Complex A C(G, A)
    (Cocycle G A) PUnit.{1} where
  d₀ := d₀ G A
  d₁ := d₁ G A
  d₂ := 0
  d₁_d₀ := d₁_d₀ G A
  d₂_d₁ _ := rfl

/-- Continuous H², as genuine Z² modulo the image of the bar differential.
The cone API's cycles add only the vacuous kernel-of-zero subtype to Z². -/
abbrev Group := (complex G A).H₂

/-- Class of a genuine continuous two-cocycle. -/
def classOf : Cocycle G A →+ H2.Continuous.Group G A where
  toFun z := (complex G A).class₂ ⟨z, rfl⟩
  map_zero' := by change (complex G A).class₂ 0 = 0; exact map_zero _
  map_add' z w := by
    change (complex G A).class₂
      ((⟨z, rfl⟩ : (complex G A).Cycles₂) + ⟨w, rfl⟩) = _
    exact map_add _ _ _

@[simp] theorem classOf_d₁ (a : C(G, A)) : classOf G A (d₁ G A a) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨a, rfl⟩

theorem classOf_eq_zero_iff (z : Cocycle G A) :
    classOf G A z = 0 ↔ ∃ a : C(G, A), d₁ G A a = z := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp h
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact classOf_d₁ G A a

theorem classOf_surjective : Function.Surjective (classOf G A) := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (complex G A).boundary₂.range q
  exact ⟨z.val, rfl⟩

end GroupCohomology.H2.Continuous
