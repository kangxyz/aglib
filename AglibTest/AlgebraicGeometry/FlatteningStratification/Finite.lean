/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Finite

/-! Focused consumer of the joint rank strata of finitely many finitely presented sheaves (Nitsure,
arXiv:math/0504590v1, proof of Theorem 4.3, p. 22), with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The joint stratum of prescribed ranks represents simultaneous local freeness of those
ranks. -/
example {S T : Scheme.{u}} {J : Type} [Finite J] (E : J → S.Modules)
    (hE : ∀ j, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S (E j))
    [∀ j, (E j).IsFinitePresentation] (e : J → ℕ) (g : T ⟶ S) :
    (∃ h : T ⟶ Scheme.Modules.jointRankStratum E hE e,
        h ≫ Scheme.Modules.jointRankStratumι E hE e = g) ↔
      ∀ j, Scheme.Modules.SheafHasRank ((Scheme.Modules.pullback g).obj (E j)) (e j) :=
  Scheme.Modules.exists_lift_jointRankStratumι_iff E hE e g

/-- The joint flattening stratification is a monomorphism representing simultaneous local
freeness. -/
example {S T : Scheme.{u}} {J : Type} [Finite J] (E : J → S.Modules)
    (hE : ∀ j, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S (E j))
    [∀ j, (E j).IsFinitePresentation] (g : T ⟶ S) :
    Mono (Scheme.Modules.jointRankStrataι E hE) ∧
      ((∃ h : T ⟶ Scheme.Modules.jointRankStrata E hE,
          h ≫ Scheme.Modules.jointRankStrataι E hE = g) ↔
        ∀ j, Scheme.Modules.IsFiniteLocallyFree T ((Scheme.Modules.pullback g).obj (E j))) :=
  ⟨Scheme.Modules.jointRankStrataι_mono E hE,
    Scheme.Modules.exists_lift_jointRankStrataι_iff E hE g⟩

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_jointRankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_jointRankStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_jointRankStrataι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_jointRankStrataι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.jointRankStrataι_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.jointRankStrataι_mono
