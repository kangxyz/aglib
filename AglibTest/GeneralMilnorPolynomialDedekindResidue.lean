/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.KTheory.MilnorK.Dedekind.PolynomialResidue
import Lean.Util.CollectAxioms

/-! # Literal polynomial-to-Dedekind residue regression checks -/

open MilnorK Polynomial IsDedekindDomain
open MilnorK.PolynomialDedekindResidue

noncomputable section

variable {k : Type*} [Field k]

example (q : HeightOneSpectrum k[X]) : point (polynomial q) = q := point_polynomial q

example (p : PolynomialResidue.MonicIrreducible k) : polynomial (point p) = p :=
  polynomial_point p

example (p : PolynomialResidue.MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    MilnorK.map n (Polynomial.LocalResidue.residueEquiv p.val).toRingHom
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
      PolynomialResidue.residueAt p.val n x := totalResidue_point p n x

open Lean in
run_cmd do
  let env ← getEnv
  for name in #[
      `MilnorK.PolynomialDedekindResidue.pointEquiv,
      `MilnorK.PolynomialDedekindResidue.fractionAlgebra_eq,
      `MilnorK.PolynomialDedekindResidue.totalResidue_point] do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Polynomial place equivalence and literal Dedekind residue bridge: standard axioms only."
