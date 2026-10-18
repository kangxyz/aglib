/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.BalancedRepresentatives
public import Lean.Util.CollectAxioms

/-! # Consumers and axiom audits for genuine Milnor K₂ generation -/

@[expose] public noncomputable section

open Polynomial MilnorK.K2

namespace AglibTest.MilnorK2BalancedRepresentatives

variable {k : Type*} [Field k] {p : k[X]} [Fact (Irreducible p)]

/-- The generated object is exactly the original integer tensor quotient. -/
theorem actual_quotient_generated (hp : p.Monic)
    (z : UnitTensor (AdjoinRoot p) ⧸ steinbergSpan (AdjoinRoot p)) :
    z ∈ Submodule.span ℤ (lowDegreeSymbols p) := by
  change z ∈ lowDegreeSpan p
  rw [lowDegreeSpan_eq_top hp]
  trivial

/-- The quadratic boundary really allows two degree-one representatives,
although their degree sum does not satisfy the strict generator bound. -/
theorem quadratic_boundary (hp : p.Monic) (hd : p.natDegree = 2)
    (A B : k[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAd : A.natDegree ≤ 1) (hBd : B.natDegree ≤ 1)
    (a b : (AdjoinRoot p)ˣ) (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (hb : (b : AdjoinRoot p) = AdjoinRoot.mk p B) :
    symbol a b ∈ lowDegreeSpan p := by
  apply symbol_mem_lowDegreeSpan_of_half_bounds hp A B hA hB
  · simpa only [hd, Nat.reduceDiv] using hAd
  · simpa only [hd, Nat.reduceDiv] using hBd
  · exact ha
  · exact hb

/-- Equality on the strict-total-degree generators determines additive maps
on the constructed group. -/
theorem maps_determined {G : Type*} [AddCommGroup G] (hp : p.Monic)
    (f g : MilnorK.K2.Group (AdjoinRoot p) →+ G)
    (h : ∀ (A B : k[X]), A ≠ 0 → B ≠ 0 → A.natDegree + B.natDegree < p.natDegree →
      ∀ (a b : (AdjoinRoot p)ˣ), (a : AdjoinRoot p) = AdjoinRoot.mk p A →
        (b : AdjoinRoot p) = AdjoinRoot.mk p B → f (symbol a b) = g (symbol a b)) :
    f = g := lowDegree_symbolHom_ext hp h

open Lean in
run_cmd do
  for name in #[``symbol_sub_mul_reduction, ``symbol_eq_mul_reduction,
      ``symbol_mem_lowDegreeSpan, ``symbol_mem_lowDegreeSpan_of_half_bounds,
      ``symbol_mem_lowDegreeSpan_all, ``lowDegreeSpan_eq_top,
      ``lowDegree_symbolHom_ext, ``actual_quotient_generated,
      ``quadratic_boundary, ``maps_determined] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual Milnor K2 small-degree generation uses only standard foundations."

end AglibTest.MilnorK2BalancedRepresentatives
