/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H2.Continuous.Cup

/-!
# Bilinearity and principal-cocycle cup primitives

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCupBilinear.lean`.
SHA-256: `32e3691b943425f490c9a00ece8df48aa1c5c2820d01c54d1e01ef3a9b3911b7`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.H2.Continuous.Cup
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)
variable {J A C : Type*} [_root_.Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction J A] [ContinuousSMul J A]
  [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [DistribMulAction J C] [ContinuousSMul J C]
variable (p : Pairing J A A C)

/-- The actual continuous cocycle cup is additive in both inputs. -/
def cocycleBilinear : ContinuousH1.Cocycle J A →+ ContinuousH1.Cocycle J A →+
    Cocycle J C where
  toFun a :=
    { toFun := fun b => H2.Continuous.Cup.cupCocycle p a b
      map_zero' := by
        apply Cocycle.ext
        intro g h
        change (p).bilinear (a.val g) (g • (0 : A)) = 0
        rw [smul_zero, map_zero]
      map_add' := by
        intro b c
        apply Cocycle.ext
        intro g h
        change (p).bilinear (a.val g) (g • (b.val h + c.val h)) = _
        rw [smul_add, map_add]
        rfl }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    apply Cocycle.ext
    intro g h
    change (p).bilinear (0 : A) (g • b.val h) = 0
    rw [map_zero]
    rfl
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro c
    apply Cocycle.ext
    intro g h
    change (p).bilinear (a.val g + b.val g) (g • c.val h) = _
    rw [map_add]
    rfl

/-- Bilinear actual cup classes, before changing either root choice. -/
def classBilinear : ContinuousH1.Cocycle J A →+ ContinuousH1.Cocycle J A →+
    H2.Continuous.Group J C where
  toFun a := (classOf J C).comp (cocycleBilinear p a)
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change classOf J C (cocycleBilinear p 0 b) = 0
    rw [map_zero]
    exact map_zero _
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro c
    change classOf J C (cocycleBilinear p (a + b) c) = _
    rw [map_add]
    change classOf J C (cocycleBilinear p a c + cocycleBilinear p b c) = _
    exact map_add _ _ _

/-- The continuous cochain `g ↦ p(v, b(g))` used as a primitive when the left cup factor is
principal. -/
def principalLeftPrimitive (v : A) (b : ContinuousH1.Cocycle J A) : C(J, C) :=
  ⟨fun g => (p).bilinear v (b.val g), (p).continuous.comp (continuous_const.prodMk b.continuous)⟩

/-- The continuous cochain `g ↦ -p(a(g), g • v)` used as a primitive when the right cup factor
is principal. -/
def principalRightPrimitive (a : ContinuousH1.Cocycle J A) (v : A) : C(J, C) :=
  ⟨fun g => -(p).bilinear (a.val g) (g • v),
    ((p).continuous.comp (a.continuous.prodMk (continuous_id.smul continuous_const))).neg⟩

theorem cup_principal_left (v : A) (b : ContinuousH1.Cocycle J A) :
    cocycleBilinear p (ContinuousH1.principal J A v) b =
      d₁ J C (principalLeftPrimitive p v b) := by
  apply Cocycle.ext
  intro g h
  change (p).bilinear (g • v - v) (g • b.val h) =
    g • (p).bilinear v (b.val h) - (p).bilinear v (b.val (g * h)) + (p).bilinear v (b.val g)
  rw [← (p).equivariant, b.map_mul]
  simp only [map_sub, AddMonoidHom.sub_apply, map_add]
  abel

theorem cup_principal_right (a : ContinuousH1.Cocycle J A) (v : A) :
    cocycleBilinear p a (ContinuousH1.principal J A v) =
      d₁ J C (principalRightPrimitive p a v) := by
  apply Cocycle.ext
  intro g h
  change (p).bilinear (a.val g) (g • (h • v - v)) =
    g • (-(p).bilinear (a.val h) (h • v)) -
      (-(p).bilinear (a.val (g * h)) ((g * h) • v)) +
      (-(p).bilinear (a.val g) (g • v))
  rw [smul_neg, ← (p).equivariant, a.map_mul]
  simp only [smul_sub, map_sub, map_add, AddMonoidHom.add_apply, mul_smul]
  abel

@[simp] theorem class_principal_left (v : A) (b : ContinuousH1.Cocycle J A) :
    classBilinear p (ContinuousH1.principal J A v) b = 0 := by
  change classOf J C (cocycleBilinear p (ContinuousH1.principal J A v) b) = 0
  rw [cup_principal_left, classOf_d₁]

@[simp] theorem class_principal_right (a : ContinuousH1.Cocycle J A) (v : A) :
    classBilinear p a (ContinuousH1.principal J A v) = 0 := by
  change classOf J C (cocycleBilinear p a (ContinuousH1.principal J A v)) = 0
  rw [cup_principal_right, classOf_d₁]


end GroupCohomology.H2.Continuous.Cup
