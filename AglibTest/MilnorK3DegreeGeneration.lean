/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.DegreeGeneration
import Lean.Util.CollectAxioms

/-! Consumers of generation, exhaustion, and the constant base stage in actual Milnor K₃. -/

open Polynomial
open MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.DegreeFiltration

noncomputable section

namespace AglibTest.MilnorK3DegreeGeneration

variable {k : Type*} [Field k]

/-- The stage is generated in the actual quotient, with no factorization premise. -/
theorem actual_stage_decomposition (d : ℕ) (hd : 0 < d) :
    lower k (d + 1) = lower k d ⊔ Submodule.span ℤ
      {x | ∃ (p a b : k[X]) (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0),
        p.Monic ∧ Irreducible p ∧ p.natDegree = d ∧
        a.natDegree < d ∧ b.natDegree < d ∧
        x = symbol3 (polynomialUnit p hp) (polynomialUnit a ha) (polynomialUnit b hb)} :=
  lower_succ_eq d hd

/-- Three simultaneous top-degree entries are covered, including repetitions. -/
theorem three_top_entries (d : ℕ) (hd : 0 < d) (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hadeg : a.natDegree = d) (hbdeg : b.natDegree = d) (hcdeg : c.natDegree = d) :
    symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
      lower k d ⊔ Submodule.span ℤ (topGenerators k d) :=
  polynomial_symbol_mem_generatedStage d hd a b c ha hb hc hadeg.le hbdeg.le hcdeg.le

/-- The repeated-factor branch retains the sign unit, rather than assuming alternation. -/
theorem repeated_top_retains_sign (p a : k[X]) (hp : p ≠ 0) (ha : a ≠ 0) :
    symbol3 (polynomialUnit p hp) (polynomialUnit p hp) (polynomialUnit a ha) =
      symbol3 (polynomialUnit p hp) (-1) (polynomialUnit a ha) :=
  symbol3_self_left _ _

/-- Exhaustion applies to every class, not only literal symbols. -/
theorem actual_class_is_bounded (x : MilnorK.K3.Group (RatFunc k)) : ∃ d : ℕ, x ∈ lower k d :=
  exists_mem_lower x

/-- The base stage uses the proved field map on the original Milnor quotient. -/
theorem actual_constant_base :
    lower k 1 = LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)) :=
  lower_one_eq_constant_range

end AglibTest.MilnorK3DegreeGeneration

open Lean in
run_cmd do
  let names := #[
    `MilnorK.K3.DegreeFiltration.lower_succ_eq,
    `MilnorK.K3.DegreeFiltration.polynomial_symbol_mem_generatedStage,
    `MilnorK.K3.DegreeFiltration.exists_mem_lower,
    `MilnorK.K3.DegreeFiltration.iSup_lower_eq_top,
    `MilnorK.K3.DegreeFiltration.lower_one_eq_constant_range]
  for name in names do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Degree generation, exhaustion, and the constant base stage use only logical foundations."
