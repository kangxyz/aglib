/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Rank

/-! Focused consumer of the rank-`r` Fitting strata (the case `n = 0` of Nitsure,
arXiv:math/0504590v1, Theorem 4.3) and their universal property, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

example {S : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) (r : ℕ) :
    IsImmersion (Scheme.Modules.rankStratumι F hF r) :=
  inferInstance

example {S T : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ Scheme.Modules.rankStratum F hF r, g' ≫ Scheme.Modules.rankStratumι F hF r = g) ↔
      (∀ k < r, Scheme.Modules.fittingIdealSheaf ((Scheme.Modules.pullback g).obj F)
          (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation
            g F) k = ⊥) ∧
        Scheme.Modules.fittingIdealSheaf ((Scheme.Modules.pullback g).obj F)
          (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation
            g F) r = ⊤ :=
  Scheme.Modules.exists_lift_rankStratumι_iff_fittingIdealSheaf F hF g _ r

example {S T : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ Scheme.Modules.rankStratum F hF r, g' ≫ Scheme.Modules.rankStratumι F hF r = g) ↔
      ∀ (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1),
        letI := (g.appLE U V h).hom.toAlgebra
        ∀ q : PrimeSpectrum Γ(T, V),
          q ∈ Module.freeLocus Γ(T, V) (Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)) ∧
            Module.rankAtStalk (Γ(T, V) ⊗[Γ(S, U)] Γ(F, U)) q = r :=
  Scheme.Modules.exists_lift_rankStratumι_iff_stalkwise F hF g r

/-- Target 3: the universal property with Aglib's finite-local-basis rank interface. -/
example {S T : Scheme.{u}} (F : S.Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType S F) [F.IsFinitePresentation]
    (g : T ⟶ S) (r : ℕ) :
    (∃ g' : T ⟶ Scheme.Modules.rankStratum F hF r, g' ≫ Scheme.Modules.rankStratumι F hF r = g) ↔
      Scheme.Modules.SheafHasRank ((Scheme.Modules.pullback g).obj F) r :=
  Scheme.Modules.exists_lift_rankStratumι_iff_sheafHasRank F hF g r

/-- The absolute criterion: Fitting conditions characterize finite local freeness of rank `r`. -/
example {T : Scheme.{u}} (G : T.Modules) [G.IsFinitePresentation]
    (hG : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType T G) (r : ℕ) :
    ((∀ k < r, Scheme.Modules.fittingIdealSheaf G hG k = ⊥) ∧
        Scheme.Modules.fittingIdealSheaf G hG r = ⊤) ↔ Scheme.Modules.SheafHasRank G r :=
  Scheme.Modules.fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank G hG r

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_sheafHasRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_sheafHasRank

/--
info: 'AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_eq_bot_and_eq_top_iff_sheafHasRank

/--
info: 'AlgebraicGeometry.Scheme.Modules.sheafRank_le_iff_notMem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.sheafRank_le_iff_notMem_support

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_fittingIdealSheaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_fittingIdealSheaf

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_stalkwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_lift_rankStratumι_iff_stalkwise
