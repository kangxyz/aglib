/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.SMulRegular

/-! Focused consumer of the restriction of nonzerodivisors on the sections over an affine open
to its basic opens and to its subopens, `AffineOpenSections.isSMulRegular_basicOpen` and
`AffineOpenSections.isSMulRegular_restrict`. Quasicoherence is assumed only on the canonical
affine chart `Spec Γ(X, U) → X`; there is no finiteness or Noetherian hypothesis. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

/-- A nonzerodivisor on the sections over an affine open restricts to its basic opens. -/
example {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] {a : Γ(X, U)} (ha : IsSMulRegular Γ(M, U) a)
    (f : Γ(X, U)) :
    IsSMulRegular Γ(M, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op a) :=
  AffineOpenSections.isSMulRegular_basicOpen M hU ha f

/-- A nonzerodivisor on the sections over an affine open restricts to every subopen; for
example, to its intersection with any open `W`. -/
example {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] {a : Γ(X, U)} (ha : IsSMulRegular Γ(M, U) a)
    (W : X.Opens) :
    IsSMulRegular Γ(M, U ⊓ W) (X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op a) :=
  AffineOpenSections.isSMulRegular_restrict M hU ha inf_le_left

/--
info: 'AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_basicOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_basicOpen

/--
info: 'AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_restrict
