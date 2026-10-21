/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Continuous.Corestriction.Basic
public import Aglib.GroupCohomology.H2.Continuous.Cup

/-!
# The continuous cup projection formula and its explicit primitive

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestriction.lean`.
SHA-256: `479e6eeeb40e0da2f9def4a40653e65cb8d5fe17062a5420175c1384ba90eca7`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.Continuous.Corestriction
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)
open GroupCohomology.H2.Continuous.Cup

variable (G : Type*) [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (hH : IsOpen (H : Set G)) [H.FiniteIndex]
/-- The `Fintype` structure on the coset space of the finite-index subgroup `H`. -/
local instance instFintypeProjectionCosets : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
variable (A B C : Type*)
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]
  [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [DistribMulAction G C] [ContinuousSMul G C]

/-- A single summand of the constructed degree-one transfer. -/
def localValue (b : ContinuousH1.Cocycle H B) (g : G) (x : G ⧸ H) : B :=
  representative G H x • b.val (factor G H g x)

omit [IsTopologicalGroup G] [H.FiniteIndex] [ContinuousSMul G B] in
theorem localValue_mul (b : ContinuousH1.Cocycle H B) (g h : G) (x : G ⧸ H) :
    localValue G H B b (g * h) x = localValue G H B b g x +
      g • localValue G H B b h (shift G H g x) := by
  simp only [localValue, factor_mul, b.map_mul, smul_add, representative_factor_smul]

omit [IsTopologicalGroup G] [H.FiniteIndex] [ContinuousSMul G A] in
/-- Restricting a global cocycle and changing the coset representative gives
this explicit degree-zero correction. -/
theorem weighted_restriction (a : ContinuousH1.Cocycle G A) (g : G) (x : G ⧸ H) :
    representative G H x • a.val (factor G H g x : G) =
      a.val g + g • a.val (representative G H (shift G H g x)) -
        a.val (representative G H x) := by
  have he := congrArg a.val (representative_factor G H g x)
  rw [a.map_mul, a.map_mul] at he
  rw [← he]
  abel

variable (p : Pairing G A B C)

/-- The finite-sum correction cochain for the cup projection formula. -/
def projectionPrimitive (a : ContinuousH1.Cocycle G A) (b : ContinuousH1.Cocycle H B) :
    C(G, C) :=
  ⟨fun g => ∑ x : G ⧸ H, p.bilinear (a.val (representative G H x)) (localValue G H B b g x), by
    apply continuous_finsetSum
    intro x hx
    exact p.continuous.comp (continuous_const.prodMk (continuous_const.smul
      (b.continuous.comp ((continuous_factor G H hH).comp
        (continuous_id.prodMk continuous_const)))))⟩

omit [ContinuousSMul G A] [ContinuousSMul G C] in
theorem projectionPrimitive_action (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle H B) (g h : G) :
    g • projectionPrimitive G H hH A B C p a b h =
      ∑ x : G ⧸ H,
        p.bilinear (g • a.val (representative G H (shift G H g x)))
          (g • localValue G H B b h (shift G H g x)) := by
  change g • (∑ x : G ⧸ H,
    p.bilinear (a.val (representative G H x)) (localValue G H B b h x)) = _
  rw [Finset.smul_sum]
  simp_rw [← p.equivariant]
  exact (sum_shift G H C g (fun x =>
    p.bilinear (g • a.val (representative G H x)) (g • localValue G H B b h x))).symm

omit [ContinuousSMul G A] in
theorem projectionPrimitive_differential (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle H B) (g h : G) :
    (d₁ G C (projectionPrimitive G H hH A B C p a b)).val (g, h) =
      ∑ x : G ⧸ H,
        p.bilinear (g • a.val (representative G H (shift G H g x)) -
          a.val (representative G H x)) (g • localValue G H B b h (shift G H g x)) := by
  rw [d₁_apply, projectionPrimitive_action]
  change (∑ x : G ⧸ H,
    p.bilinear (g • a.val (representative G H (shift G H g x)))
      (g • localValue G H B b h (shift G H g x))) -
    (∑ x : G ⧸ H, p.bilinear (a.val (representative G H x)) (localValue G H B b (g * h) x)) +
    (∑ x : G ⧸ H, p.bilinear (a.val (representative G H x)) (localValue G H B b g x)) = _
  simp_rw [localValue_mul, map_add, map_sub, AddMonoidHom.sub_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

omit [ContinuousSMul G A] in
theorem transfer_restrictedCup_apply (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle H B) (g h : G) :
    (transferCocycles₂ G H hH C
      (cupCocycle (restrictPairing p H) (restrictCocycle H a) b)).val (g, h) =
      ∑ x : G ⧸ H,
        p.bilinear (a.val g + g • a.val (representative G H (shift G H g x)) -
          a.val (representative G H x)) (g • localValue G H B b h (shift G H g x)) := by
  change (∑ x : G ⧸ H,
    representative G H x • p.bilinear (a.val (factor G H g x : G))
      (factor G H g x • b.val (factor G H h (shift G H g x)))) = _
  apply Finset.sum_congr rfl
  intro x hx
  rw [← p.equivariant, weighted_restriction]
  congr 1
  exact representative_factor_smul G H B g x (b.val (factor G H h (shift G H g x)))

omit [ContinuousSMul G A] in
/-- The projection formula holds on native continuous cocycles up to the
displayed, genuinely continuous finite-sum primitive. -/
theorem projectionFormula_cocycle (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle H B) :
    transferCocycles₂ G H hH C
      (cupCocycle (restrictPairing p H) (restrictCocycle H a) b) =
        cupCocycle p a (transferCocycles₁ G H hH B b) +
          d₁ G C (projectionPrimitive G H hH A B C p a b) := by
  apply Cocycle.ext
  intro g h
  change _ = (cupCocycle p a (transferCocycles₁ G H hH B b)).val (g, h) +
    (d₁ G C (projectionPrimitive G H hH A B C p a b)).val (g, h)
  rw [transfer_restrictedCup_apply, projectionPrimitive_differential, cupCocycle_apply]
  change (∑ x : G ⧸ H,
    p.bilinear (a.val g + g • a.val (representative G H (shift G H g x)) -
      a.val (representative G H x)) (g • localValue G H B b h (shift G H g x))) =
    p.bilinear (a.val g) (g • ∑ x : G ⧸ H, localValue G H B b h x) + _
  have hs := sum_shift G H C g (fun x => p.bilinear (a.val g) (g • localValue G H B b h x))
  simp only [map_sub, map_add, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
  rw [Finset.smul_sum, map_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hs]
  abel

omit [ContinuousSMul G A] in
/-- The first actual cup projection-formula supplier on native continuous H2. -/
theorem projectionFormula (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle H B) :
    corestriction₂ G H hH C
      (classOf H C (cupCocycle (restrictPairing p H) (restrictCocycle H a) b)) =
        classOf G C (cupCocycle p a (transferCocycles₁ G H hH B b)) := by
  rw [corestriction₂_class, projectionFormula_cocycle, map_add, classOf_d₁, add_zero]


end GroupCohomology.Continuous.Corestriction
