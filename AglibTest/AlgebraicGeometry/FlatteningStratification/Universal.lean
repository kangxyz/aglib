/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Universal

/-! Focused consumer of the stratification by fibre rank and of the local universal flattening
property of the rank strata (Stacks Project, Tag 05P9; Nitsure, arXiv:math/0504590v1,
Theorem 4.3, case `n = 0`), with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- Each stratum is a monomorphism into the base (immersions are monomorphisms). -/
example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) (r : ℕ) :
    Mono (Scheme.Modules.rankStratumι F hF r) :=
  inferInstance

example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (y : S) (r : ℕ) :
    y ∈ Set.range (Scheme.Modules.rankStratumι F hF r) ↔ Scheme.Modules.sheafRank F y = r :=
  Scheme.Modules.mem_range_rankStratumι_iff F hF y r

example {S T : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (g : T ⟶ S) :
    Scheme.Modules.IsFiniteLocallyFree T ((Scheme.Modules.pullback g).obj F) ↔
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
        ∃ g' : U.toScheme ⟶ Scheme.Modules.rankStratum F hF r,
          g' ≫ Scheme.Modules.rankStratumι F hF r = U.ι ≫ g :=
  Scheme.Modules.isFiniteLocallyFree_pullback_iff F hF g

/--
info: 'AlgebraicGeometry.Scheme.Modules.mem_range_rankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.mem_range_rankStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.sheafRank_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.sheafRank_pullback

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.range_locallyClosedι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.range_locallyClosedι
