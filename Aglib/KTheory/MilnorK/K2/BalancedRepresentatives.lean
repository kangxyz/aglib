/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DegreeBound

/-!
# Small-total-degree generators for the actual Milnor K₂ quotient

Balanced polynomial fractions reduce every symbol to symbols with two
half-degree entries. Leading-term cancellation handles the even-degree
boundary. Tensor and quotient induction then prove generation of the actual
Milnor group, without a generation premise or a restriction to symbols with
one entry in the original base field.
-/

@[expose] public noncomputable section

open Polynomial

namespace MilnorK.K2

variable {k : Type*} [Field k] {p : k[X]} [Fact (Irreducible p)]

/-- Every symbol in the root field belongs to the integer span of symbols
whose polynomial representatives have total degree below the extension degree. -/
theorem symbol_mem_lowDegreeSpan_all (hp : p.Monic) (x y : (AdjoinRoot p)ˣ) :
    symbol x y ∈ lowDegreeSpan p := by
  have hn : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  obtain ⟨A, B, hA, hB, hAd, hBd, hx⟩ :=
    AdjoinRoot.exists_balanced_fraction hp (x : AdjoinRoot p) x.ne_zero
  obtain ⟨C, D, hC, hD, hCd, hDd, hy⟩ :=
    AdjoinRoot.exists_balanced_fraction hp (y : AdjoinRoot p) y.ne_zero
  have hBd' : B.natDegree ≤ p.natDegree / 2 := by omega
  have hDd' : D.natDegree ≤ p.natDegree / 2 := by omega
  let a : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p A)
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hA (by omega))
  let b : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p B)
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hB (by omega))
  let c : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p C)
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hC (by omega))
  let d : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p D)
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hD (by omega))
  have hx' : x = a / b := Units.ext hx
  have hy' : y = c / d := Units.ext hy
  rw [hx', hy', symbol_div_left, symbol_div_right, symbol_div_right]
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · exact symbol_mem_lowDegreeSpan_of_half_bounds hp A C hA hC hAd hCd a c rfl rfl
    · exact symbol_mem_lowDegreeSpan_of_half_bounds hp A D hA hD hAd hDd' a d rfl rfl
  · apply Submodule.sub_mem
    · exact symbol_mem_lowDegreeSpan_of_half_bounds hp B C hB hC hBd' hCd b c rfl rfl
    · exact symbol_mem_lowDegreeSpan_of_half_bounds hp B D hB hD hBd' hDd' b d rfl rfl

/-- Small-total-degree polynomial symbols additively generate the genuine
integer tensor quotient defining Milnor K₂ of the root field. -/
theorem lowDegreeSpan_eq_top (hp : p.Monic) : lowDegreeSpan p = ⊤ := by
  apply top_unique
  intro z _
  refine Submodule.Quotient.induction_on _ z ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact symbol_mem_lowDegreeSpan_all hp a.toMul b.toMul
  | add t s ht hs =>
      change (steinbergSpan (AdjoinRoot p)).mkQ (t + s) ∈ lowDegreeSpan p
      rw [map_add]
      exact Submodule.add_mem _ ht hs

/-- Additive maps out of the actual Milnor quotient are determined by the
small-total-degree polynomial symbols. -/
theorem lowDegree_symbolHom_ext {G : Type*} [AddCommGroup G] (hp : p.Monic)
    {f g : Group (AdjoinRoot p) →+ G}
    (h : ∀ (A B : k[X]), A ≠ 0 → B ≠ 0 → A.natDegree + B.natDegree < p.natDegree →
      ∀ (a b : (AdjoinRoot p)ˣ), (a : AdjoinRoot p) = AdjoinRoot.mk p A →
        (b : AdjoinRoot p) = AdjoinRoot.mk p B → f (symbol a b) = g (symbol a b)) :
    f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply LinearMap.ext_on (s := lowDegreeSymbols p) (lowDegreeSpan_eq_top hp)
  rintro z ⟨A, B, hA, hB, hdeg, a, b, ha, hb, rfl⟩
  exact h A B hA hB hdeg a b ha hb

end MilnorK.K2
