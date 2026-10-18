/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Coproduct

/-! Focused consumer of the disjoint union of the rank strata and its universal property
(Stacks Project, Tag 05P9; Nitsure, arXiv:math/0504590v1, Theorem 4.3 (ii), case `n = 0`), with
axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The disjoint union of the strata is a monomorphism into the base. -/
example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation] :
    Mono (Scheme.Modules.rankStrataι F hF) :=
  Scheme.Modules.rankStrataι_mono F hF

/-- It represents the subfunctor of morphisms along which `F` pulls back to a finite locally free
sheaf. -/
example {S T : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (g : T ⟶ S) :
    (∃ h : T ⟶ ∐ fun r : ℕ => Scheme.Modules.rankStratum F hF r,
        h ≫ Sigma.desc (Scheme.Modules.rankStratumι F hF) = g) ↔
      Scheme.Modules.IsFiniteLocallyFree T ((Scheme.Modules.pullback g).obj F) :=
  Scheme.Modules.exists_lift_rankStrataι_iff F hF g

/--
info: 'AlgebraicGeometry.Scheme.Modules.rankStrataι_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.rankStrataι_mono

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_rankStrataι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_rankStrataι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.mem_range_sigmaι_rankStratum_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.mem_range_sigmaι_rankStratum_iff
