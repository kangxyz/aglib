/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Closed

/-! Focused consumer of the closed joint rank strata and of the closure of the rank strata
(Nitsure, arXiv:math/0504590v1, proof of Theorem 4.3, pp. 20 and 22), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {S T : Scheme.{u}} {I : Type} (E : I → S.Modules)
    (hE : ∀ i, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S (E i))
    [∀ i, (E i).IsFinitePresentation] (e : I → ℕ)
    (hrank : ∀ i y, Scheme.Modules.sheafRank (E i) y ≤ e i) (g : T ⟶ S) :
    (∃ g' : T ⟶ Scheme.Modules.closedJointRankStratum E hE e,
        g' ≫ Scheme.Modules.closedJointRankStratumι E hE e = g) ↔
      ∀ i, Scheme.Modules.SheafHasRank ((Scheme.Modules.pullback g).obj (E i)) (e i) :=
  Scheme.Modules.exists_lift_closedJointRankStratumι_iff E hE e hrank g

example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (r : ℕ) :
    closure (Set.range (Scheme.Modules.rankStratumι F hF r)) ⊆
      ⋃ (r' : ℕ) (_ : r ≤ r'), Set.range (Scheme.Modules.rankStratumι F hF r') :=
  Scheme.Modules.closure_range_rankStratumι_subset F hF r

/-- The refined joint stratum `S_f` of Nitsure's proof: a finite open condition, a possibly
infinite closed condition. -/
example {S T : Scheme.{u}} {I : Type} (E : I → S.Modules)
    (hE : ∀ i, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S (E i))
    [∀ i, (E i).IsFinitePresentation] (e : I → ℕ) (J₀ : Finset I)
    (H : ∀ y : S, (∀ j ∈ J₀, Scheme.Modules.sheafRank (E j) y = e j) →
      ∀ i, Scheme.Modules.sheafRank (E i) y ≤ e i) (g : T ⟶ S) :
    IsImmersion (Scheme.Modules.refinedJointRankStratumι E hE e J₀) ∧
      ((∃ g' : T ⟶ Scheme.Modules.refinedJointRankStratum E hE e J₀,
          g' ≫ Scheme.Modules.refinedJointRankStratumι E hE e J₀ = g) ↔
        ∀ i, Scheme.Modules.SheafHasRank ((Scheme.Modules.pullback g).obj (E i)) (e i)) :=
  ⟨inferInstance, Scheme.Modules.exists_lift_refinedJointRankStratumι_iff E hE e J₀ H g⟩

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_refinedJointRankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_refinedJointRankStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_closedJointRankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_closedJointRankStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.closure_range_rankStratumι_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.closure_range_rankStratumι_subset
