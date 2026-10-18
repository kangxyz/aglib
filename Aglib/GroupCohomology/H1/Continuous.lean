/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Abel

/-!
# Continuous first cohomology

Source: the reviewed `WeightTwoBockstein/ContinuousH1.lean` at immutable
archive revision `39cf3ab`, SHA-256
`879d1f892f396c14d1a4acadaee32b5f9a32d8d1f53dd7864967526acfc9a8fa`.
The common construction is absorbed here without a second general H¹ interface.

This file constructs `H¹_cont(G, A)` as the quotient of continuous crossed
homomorphisms by principal crossed homomorphisms. The topology on `G` and `A`
is retained: a cochain is a bundled continuous map, not an arbitrary function.
The coefficient action is a genuine `DistribMulAction` and is jointly continuous.
No discreteness assumption is imposed on either topology.

The construction only needs the additive group underlying the coefficient module.
Thus it applies, in particular, to topological modules with a continuous additive
`G`-action. A topology on `G` suffices for these degree-one constructions, so the
results apply to topological groups without unnecessarily assuming continuity of
multiplication when it is not used in the proofs.
-/

@[expose] public section

namespace GroupCohomology.ContinuousH1

variable (G A : Type*) [Group G] [TopologicalSpace G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A]

/-- Continuous crossed homomorphisms, as an additive subgroup of continuous maps. -/
def cocycles : AddSubgroup C(G, A) where
  carrier := {c | ∀ g h : G, c (g * h) = c g + g • c h}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd g h
    simp only [ContinuousMap.add_apply, hc g h, hd g h, smul_add]
    abel
  neg_mem' := by
    intro c hc g h
    simp only [ContinuousMap.neg_apply, hc g h, smul_neg, neg_add]

/-- A continuous one-cocycle. -/
abbrev Cocycle : Type _ := ↥(cocycles G A)

namespace Cocycle

variable {G A}

/-- The crossed-homomorphism law. -/
theorem map_mul (c : Cocycle G A) (g h : G) :
    c.val (g * h) = c.val g + g • c.val h := c.property g h

/-- Continuity is part of the type of every cocycle. -/
theorem continuous (c : Cocycle G A) : Continuous c.val := c.val.continuous

@[ext] theorem ext {c d : Cocycle G A} (h : ∀ g, c.val g = d.val g) : c = d :=
  Subtype.ext (ContinuousMap.ext h)

@[simp] theorem zero_apply (g : G) : (0 : Cocycle G A).val g = 0 := rfl
@[simp] theorem add_apply (c d : Cocycle G A) (g : G) :
    (c + d).val g = c.val g + d.val g := rfl
@[simp] theorem neg_apply (c : Cocycle G A) (g : G) :
    (-c).val g = -c.val g := rfl
@[simp] theorem sub_apply (c d : Cocycle G A) (g : G) :
    (c - d).val g = c.val g - d.val g := rfl

@[simp] theorem map_one (c : Cocycle G A) : c.val 1 = 0 := by
  have h := c.map_mul 1 1
  exact (add_left_cancel (show c.val 1 + 0 = c.val 1 + c.val 1 by simpa using h)).symm

end Cocycle

variable [ContinuousSMul G A]

/-- The principal cocycle associated to `a` is `g ↦ g • a - a`. -/
def principal : A →+ Cocycle G A where
  toFun a := ⟨⟨fun g => g • a - a,
    (continuous_id.smul continuous_const).sub continuous_const⟩, by
      intro g h
      simp only [ContinuousMap.coe_mk, mul_smul, smul_sub]
      abel⟩
  map_zero' := by ext g; simp
  map_add' := by intro a b; ext g; simp only [ContinuousMap.coe_mk, smul_add,
    Cocycle.add_apply]; abel

@[simp] theorem principal_apply (a : A) (g : G) :
    (principal G A a).val g = g • a - a := rfl

/-- Continuous coboundaries form the image of the principal-cocycle map. -/
def coboundaries : AddSubgroup (Cocycle G A) := (principal G A).range

/-- Continuous first cohomology as an additive quotient. -/
abbrev H1 := Cocycle G A ⧸ coboundaries G A

/-- The class of a continuous cocycle. -/
def classOf : Cocycle G A →+ H1 G A := QuotientAddGroup.mk' (coboundaries G A)

@[simp] theorem classOf_principal (a : A) : classOf G A (principal G A a) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact ⟨a, rfl⟩

/-- A continuous class vanishes exactly when it has a principal representative. -/
theorem classOf_eq_zero_iff (c : Cocycle G A) :
    classOf G A c = 0 ↔ ∃ a : A, principal G A a = c := by
  exact QuotientAddGroup.eq_zero_iff c

/-- Every cohomology class has a continuous cocycle representative. -/
theorem classOf_surjective : Function.Surjective (classOf G A) :=
  QuotientAddGroup.mk'_surjective (coboundaries G A)

/-- Two continuous cocycles represent the same class exactly when their
    difference is principal. -/
theorem classOf_eq_iff (c d : Cocycle G A) :
    classOf G A c = classOf G A d ↔ ∃ a : A, principal G A a = c - d := by
  rw [← sub_eq_zero, ← map_sub, classOf_eq_zero_iff]

variable (B : Type*) [AddCommGroup B] [TopologicalSpace B]
  [IsTopologicalAddGroup B] [DistribMulAction G B] [ContinuousSMul G B]

/-- A continuous additive coefficient map commuting with the genuine `G`-actions. -/
structure CoefficientMap extends ContinuousAddMonoidHom A B where
  map_smul' : ∀ (g : G) (a : A), toFun (g • a) = g • toFun a

namespace CoefficientMap

variable {G A B}

instance : CoeFun (CoefficientMap G A B) (fun _ => A → B) := ⟨fun f => f.toFun⟩

section Basic

omit [TopologicalSpace G] [IsTopologicalAddGroup A] [ContinuousSMul G A]
  [IsTopologicalAddGroup B] [ContinuousSMul G B]

-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem map_smul (f : CoefficientMap G A B) (g : G) (a : A) :
    f (g • a) = g • f a := f.map_smul' g a
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem map_zero (f : CoefficientMap G A B) : f 0 = 0 :=
  f.toContinuousAddMonoidHom.map_zero
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem map_add (f : CoefficientMap G A B) (a b : A) :
    f (a + b) = f a + f b := f.toContinuousAddMonoidHom.map_add a b
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem map_sub (f : CoefficientMap G A B) (a b : A) :
    f (a - b) = f a - f b := f.toContinuousAddMonoidHom.map_sub a b

theorem continuous (f : CoefficientMap G A B) : Continuous f :=
  f.toContinuousAddMonoidHom.continuous

end Basic

/-- Postcomposition on continuous cocycles. -/
def onCocycles (f : CoefficientMap G A B) : Cocycle G A →+ Cocycle G B where
  toFun c := ⟨⟨fun g => f (c.val g), f.continuous.comp c.continuous⟩, by
    intro g h
    simp only [ContinuousMap.coe_mk, c.map_mul, f.map_add, f.map_smul]⟩
  map_zero' := by ext g; exact f.map_zero
  map_add' := by intro c d; ext g; exact f.map_add _ _

omit [ContinuousSMul G A] [ContinuousSMul G B] in
@[simp] theorem onCocycles_apply (f : CoefficientMap G A B) (c : Cocycle G A) (g : G) :
    (f.onCocycles c).val g = f (c.val g) := rfl

@[simp] theorem onCocycles_principal (f : CoefficientMap G A B) (a : A) :
    f.onCocycles (principal G A a) = principal G B (f a) := by
  ext g
  simp only [onCocycles_apply, principal_apply, f.map_sub, f.map_smul]

/-- Equivariance makes postcomposition preserve continuous coboundaries. -/
theorem preserves_coboundaries (f : CoefficientMap G A B) :
    coboundaries G A ≤ (coboundaries G B).comap f.onCocycles := by
  rintro c ⟨a, rfl⟩
  exact ⟨f a, (f.onCocycles_principal a).symm⟩

/-- The induced map on actual continuous first cohomology. -/
def onH1 (f : CoefficientMap G A B) : H1 G A →+ H1 G B :=
  QuotientAddGroup.map (coboundaries G A) (coboundaries G B)
    f.onCocycles f.preserves_coboundaries

@[simp] theorem onH1_classOf (f : CoefficientMap G A B) (c : Cocycle G A) :
    f.onH1 (classOf G A c) = classOf G B (f.onCocycles c) := rfl

/-- The identity coefficient map. -/
def id : CoefficientMap G A A where
  toContinuousAddMonoidHom := ContinuousAddMonoidHom.id A
  map_smul' _ _ := rfl

variable {D : Type*} [AddCommGroup D] [TopologicalSpace D]
  [IsTopologicalAddGroup D] [DistribMulAction G D] [ContinuousSMul G D]

/-- Composition of continuous equivariant coefficient maps. -/
def comp (g : CoefficientMap G B D) (f : CoefficientMap G A B) :
    CoefficientMap G A D where
  toContinuousAddMonoidHom := g.toContinuousAddMonoidHom.comp f.toContinuousAddMonoidHom
  map_smul' h a := by exact (congrArg g (f.map_smul h a)).trans (g.map_smul h (f a))

omit [TopologicalSpace G] [IsTopologicalAddGroup A] [ContinuousSMul G A] in
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem id_apply (a : A) : (id : CoefficientMap G A A) a = a := rfl
omit [TopologicalSpace G] [IsTopologicalAddGroup A] [ContinuousSMul G A]
  [IsTopologicalAddGroup B] [ContinuousSMul G B]
  [IsTopologicalAddGroup D] [ContinuousSMul G D] in
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF]
theorem comp_apply (g : CoefficientMap G B D) (f : CoefficientMap G A B) (a : A) :
    g.comp f a = g (f a) := rfl

omit [ContinuousSMul G A] in
@[simp] theorem onCocycles_id :
    (id : CoefficientMap G A A).onCocycles = AddMonoidHom.id _ := by
  ext c g
  rfl

omit [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G D] in
@[simp] theorem onCocycles_comp (g : CoefficientMap G B D) (f : CoefficientMap G A B) :
    (g.comp f).onCocycles = g.onCocycles.comp f.onCocycles := by
  ext c h
  rfl

@[simp] theorem onH1_id : (id : CoefficientMap G A A).onH1 = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro c
  change classOf G A ((id : CoefficientMap G A A).onCocycles c) = classOf G A c
  rw [onCocycles_id]
  rfl

@[simp] theorem onH1_comp (g : CoefficientMap G B D) (f : CoefficientMap G A B) :
    (g.comp f).onH1 = g.onH1.comp f.onH1 := by
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro c
  change classOf G D ((g.comp f).onCocycles c) =
    classOf G D (g.onCocycles (f.onCocycles c))
  rw [onCocycles_comp]
  rfl

end CoefficientMap
end GroupCohomology.ContinuousH1

namespace GroupCohomology.ContinuousH1

section Pullback

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable {A B : Type*} [AddCommGroup A] [TopologicalSpace A]
  [AddCommGroup B] [TopologicalSpace B] [DistribMulAction G A] [DistribMulAction H B]

/-- A continuous coefficient map equivariant relative to a continuous group map.
It induces contravariance in the group and covariance in the coefficients. -/
structure PullbackMap (φ : ContinuousMonoidHom H G) extends ContinuousAddMonoidHom A B where
  map_smul' : ∀ (h : H) (a : A), toFun (φ h • a) = h • toFun a

namespace PullbackMap

variable {φ : ContinuousMonoidHom H G}

instance : CoeFun (PullbackMap (A := A) (B := B) φ) (fun _ => A → B) :=
  ⟨fun f => f.toFun⟩

-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem map_smul (f : PullbackMap (A := A) (B := B) φ) (h : H) (a : A) :
    f (φ h • a) = h • f a := f.map_smul' h a

-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem map_add (f : PullbackMap (A := A) (B := B) φ) (a b : A) :
    f (a + b) = f a + f b := f.toContinuousAddMonoidHom.map_add a b

-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF] theorem map_sub (f : PullbackMap (A := A) (B := B) φ) (a b : A) :
    f (a - b) = f a - f b := f.toContinuousAddMonoidHom.map_sub a b

variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

/-- Pullback of continuous cocycles along the group map and the coefficient map. -/
def onCocycles (f : PullbackMap (A := A) (B := B) φ) : Cocycle G A →+ Cocycle H B where
  toFun c := ⟨⟨fun h => f (c.val (φ h)),
    f.toContinuousAddMonoidHom.continuous.comp (c.val.continuous.comp φ.continuous)⟩, by
      intro h k
      change f (c.val (φ (h * k))) = f (c.val (φ h)) + h • f (c.val (φ k))
      rw [_root_.map_mul φ, Cocycle.map_mul, f.map_add]
      rw [f.map_smul]⟩
  map_zero' := by ext h; exact f.toContinuousAddMonoidHom.map_zero
  map_add' := by intro c d; ext h; exact f.toContinuousAddMonoidHom.map_add _ _

@[simp] theorem onCocycles_apply (f : PullbackMap (A := A) (B := B) φ)
    (c : Cocycle G A) (h : H) : (f.onCocycles c).val h = f (c.val (φ h)) := rfl

variable [ContinuousSMul G A] [ContinuousSMul H B]

@[simp] theorem onCocycles_principal (f : PullbackMap (A := A) (B := B) φ) (a : A) :
    f.onCocycles (principal G A a) = principal H B (f a) := by
  ext h
  change f (φ h • a - a) = h • f a - f a
  rw [f.map_sub, f.map_smul]

/-- The relative equivariance relation guarantees descent to cohomology. -/
theorem preserves_coboundaries (f : PullbackMap (A := A) (B := B) φ) :
    coboundaries G A ≤ (coboundaries H B).comap f.onCocycles := by
  rintro c ⟨a, rfl⟩
  exact ⟨f a, (f.onCocycles_principal a).symm⟩

/-- Simultaneous continuous group pullback and equivariant coefficient pushforward. -/
def onH1 (f : PullbackMap (A := A) (B := B) φ) : H1 G A →+ H1 H B :=
  QuotientAddGroup.map (coboundaries G A) (coboundaries H B)
    f.onCocycles f.preserves_coboundaries

@[simp] theorem onH1_classOf (f : PullbackMap (A := A) (B := B) φ) (c : Cocycle G A) :
    f.onH1 (classOf G A c) = classOf H B (f.onCocycles c) := rfl

end PullbackMap
end Pullback

section Restriction

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DistribMulAction G A]

/-- The actual restricted action is `h • a := φ h • a`. -/
abbrev restrictedAction (φ : ContinuousMonoidHom H G) : DistribMulAction H A :=
  DistribMulAction.compHom A φ.toMonoidHom

/-- Joint continuity of the action is preserved under continuous group pullback. -/
theorem restrictedAction_continuous [ContinuousSMul G A] (φ : ContinuousMonoidHom H G) :
    letI := restrictedAction A φ
    ContinuousSMul H A := by
  let _ := restrictedAction A φ
  exact ⟨(φ.continuous.comp continuous_fst).smul continuous_snd⟩

/-- The identity of the underlying coefficient group is equivariant for the
    restricted action and the original action relative to `φ`. -/
def restrictionMap (φ : ContinuousMonoidHom H G) :
    letI := restrictedAction A φ
    PullbackMap (A := A) (B := A) φ := by
  letI := restrictedAction A φ
  exact { toContinuousAddMonoidHom := ContinuousAddMonoidHom.id A, map_smul' := fun _ _ => rfl }

variable [IsTopologicalAddGroup A]

/-- Restriction on continuous cocycles, with the canonical restricted action. -/
def restrictionCocycles (φ : ContinuousMonoidHom H G) :
    letI := restrictedAction A φ
    Cocycle G A →+ Cocycle H A := by
  letI := restrictedAction A φ
  exact (restrictionMap A φ).onCocycles

@[simp] theorem restrictionCocycles_apply (φ : ContinuousMonoidHom H G)
    (c : Cocycle G A) (h : H) :
    letI := restrictedAction A φ
    (restrictionCocycles A φ c).val h = c.val (φ h) := rfl

variable [ContinuousSMul G A]

/-- Restriction on continuous first cohomology along a continuous group map.
The target uses the canonical restricted action, whose continuity is proved above. -/
def restriction (φ : ContinuousMonoidHom H G) :
    letI := restrictedAction A φ
    letI := restrictedAction_continuous A φ
    H1 G A →+ H1 H A := by
  letI := restrictedAction A φ
  letI := restrictedAction_continuous A φ
  exact (restrictionMap A φ).onH1

@[simp] theorem restriction_classOf (φ : ContinuousMonoidHom H G) (c : Cocycle G A) :
    letI := restrictedAction A φ
    letI := restrictedAction_continuous A φ
    restriction A φ (classOf G A c) = classOf H A (restrictionCocycles A φ c) := rfl

/-- Restriction along the identity group map is the identity on cohomology. -/
@[simp] theorem restriction_id :
    restriction A (ContinuousMonoidHom.id G) = AddMonoidHom.id (H1 G A) := by
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro c
  change classOf G A _ = classOf G A c
  congr 1

/-- Continuous group restriction is contravariantly functorial. The coefficient
    action after two restrictions is definitionally the action of the composite. -/
theorem restriction_comp {J : Type*} [Group J] [TopologicalSpace J]
    (φ : ContinuousMonoidHom H G) (ψ : ContinuousMonoidHom J H) :
    letI := restrictedAction A φ
    letI := restrictedAction_continuous A φ
    restriction A (φ.comp ψ) = (restriction A ψ).comp (restriction A φ) := by
  let _ := restrictedAction A φ
  let _ := restrictedAction_continuous A φ
  let _ := restrictedAction A ψ
  let _ := restrictedAction_continuous A ψ
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro c
  change classOf J A _ = classOf J A _
  congr 1

end Restriction
end GroupCohomology.ContinuousH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 79259e385cc1901e8641e8ca245007ebc4f1c38f1520d1b362326e511a2a837d.
Definitions, hypotheses and universes are retained modulo native names. -/
