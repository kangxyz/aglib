/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootBalancedFractions
public import Lean.Util.CollectAxioms

/-! # Consumers of balanced fractions, including the linear boundary -/

@[expose] public noncomputable section

open Polynomial

namespace AglibTest.AdjoinRootBalancedFractions

variable {k : Type*} [Field k] {p : k[X]} [Fact (Irreducible p)]

/-- The degree-one boundary has two constant nonzero representatives. -/
theorem degree_one (hp : p.Monic) (hd : p.natDegree = 1)
    (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree = 0 ∧ B.natDegree = 0 ∧
      x = AdjoinRoot.mk p A / AdjoinRoot.mk p B := by
  obtain ⟨A, B, hA, hB, hAd, hBd, h⟩ := AdjoinRoot.exists_balanced_fraction hp x hx
  simp only [hd, Nat.reduceDiv, Nat.sub_self, Nat.zero_div, Nat.le_zero] at hAd hBd
  exact ⟨A, B, hA, hB, hAd, hBd, h⟩

/-- The odd-degree bounds add to one less than the extension degree. -/
theorem odd_degree (hp : p.Monic) (d : ℕ) (hd : p.natDegree = 2 * d + 1)
    (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ d ∧ B.natDegree ≤ d ∧
      x = AdjoinRoot.mk p A / AdjoinRoot.mk p B := by
  obtain ⟨A, B, hA, hB, hAd, hBd, h⟩ := AdjoinRoot.exists_balanced_fraction hp x hx
  exact ⟨A, B, hA, hB, by omega, by omega, h⟩

/-- Even degree gives the strict denominator bound needed in the four-term expansion. -/
theorem even_degree (hp : p.Monic) (d : ℕ) (hd : p.natDegree = 2 * d)
    (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ d ∧ B.natDegree < d ∧
      x = AdjoinRoot.mk p A / AdjoinRoot.mk p B := by
  obtain ⟨A, B, hA, hB, hAd, hBd, h⟩ := AdjoinRoot.exists_balanced_fraction hp x hx
  have hn : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  exact ⟨A, B, hA, hB, by omega, by omega, h⟩

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.exists_fraction_of_degree_bounds,
      ``AdjoinRoot.exists_balanced_fraction, ``Polynomial.degree_sub_leadingRatio_mul_lt,
      ``degree_one, ``odd_degree, ``even_degree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Balanced fractions use only standard foundations."

end AglibTest.AdjoinRootBalancedFractions
