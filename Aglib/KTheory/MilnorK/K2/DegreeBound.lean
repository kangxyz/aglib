/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.KTheory.MilnorK.K2.DegreeReduction
public import Aglib.RingTheory.AdjoinRootBalancedFractions

/-!
# Low-degree symbols in a simple field extension

We define the span of symbols represented by nonzero polynomial pairs whose
total degree is smaller than the defining polynomial degree. Two polynomial
entries bounded by half that degree already lie in this span: in the boundary
case, leading-coefficient cancellation and the Steinberg relation reduce the
total degree strictly.
-/

@[expose] public noncomputable section

open Polynomial

namespace MilnorK.K2

variable {k : Type*} [Field k]

/-- Symbols admitting polynomial entries whose total degree is strictly less
than the degree of the defining irreducible polynomial. -/
def lowDegreeSymbols (p : k[X]) [Fact (Irreducible p)] : Set (Group (AdjoinRoot p)) :=
  {z | ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree + B.natDegree < p.natDegree ∧
    ∃ a b : (AdjoinRoot p)ˣ, (a : AdjoinRoot p) = AdjoinRoot.mk p A ∧
      (b : AdjoinRoot p) = AdjoinRoot.mk p B ∧ z = symbol a b}

/-- The integer span of the low-degree polynomial symbols. -/
def lowDegreeSpan (p : k[X]) [Fact (Irreducible p)] : Submodule ℤ (Group (AdjoinRoot p)) :=
  Submodule.span ℤ (lowDegreeSymbols p)

/-- The explicit polynomial witnesses put a symbol in the low-degree span. -/
theorem symbol_mem_lowDegreeSpan (p : k[X]) [Fact (Irreducible p)]
    (A B : k[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree)
    (a b : (AdjoinRoot p)ˣ) (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (hb : (b : AdjoinRoot p) = AdjoinRoot.mk p B) :
    symbol a b ∈ lowDegreeSpan p :=
  Submodule.subset_span ⟨A, B, hA, hB, hdeg, a, b, ha, hb, rfl⟩

variable {p : k[X]} [Fact (Irreducible p)]

/-- A sign symbol is low-degree whenever its polynomial entry has degree below
the defining polynomial degree. -/
theorem symbol_neg_one_mem_lowDegreeSpan (A : k[X]) (hA : A ≠ 0)
    (hdeg : A.natDegree < p.natDegree) (a : (AdjoinRoot p)ˣ)
    (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A) :
    symbol a (-1) ∈ lowDegreeSpan p := by
  apply symbol_mem_lowDegreeSpan p A (Polynomial.C (-1 : k)) hA (by simp)
    (by simpa only [natDegree_C, add_zero] using hdeg) a (-1) ha
  simp

/-- Polynomial representatives each bounded by half the defining degree give
a symbol in the strict-total-degree span. The boundary case is reduced using
the actual Steinberg relation and leading-coefficient cancellation. -/
theorem symbol_mem_lowDegreeSpan_of_half_bounds (hp : p.Monic)
    (A C : k[X]) (hA : A ≠ 0) (hC : C ≠ 0)
    (hAd : A.natDegree ≤ p.natDegree / 2) (hCd : C.natDegree ≤ p.natDegree / 2)
    (a c : (AdjoinRoot p)ˣ) (ha : (a : AdjoinRoot p) = AdjoinRoot.mk p A)
    (hc : (c : AdjoinRoot p) = AdjoinRoot.mk p C) :
    symbol a c ∈ lowDegreeSpan p := by
  by_cases hsum : A.natDegree + C.natDegree < p.natDegree
  · exact symbol_mem_lowDegreeSpan p A C hA hC hsum a c ha hc
  have hn : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hdeg : A.natDegree = C.natDegree := by omega
  have hAlt : A.natDegree < p.natDegree := by omega
  have hClt : C.natDegree < p.natDegree := by omega
  let lcoeff : k := C.leadingCoeff / A.leadingCoeff
  have hlcoeff : lcoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr hC) (leadingCoeff_ne_zero.mpr hA)
  have hL : Polynomial.C lcoeff ≠ 0 := C_ne_zero.mpr hlcoeff
  have hLdeg : (Polynomial.C lcoeff).natDegree < p.natDegree := by
    simpa only [natDegree_C] using hn
  let l : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p (Polynomial.C lcoeff))
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hL hLdeg)
  have hl : (l : AdjoinRoot p) = AdjoinRoot.mk p (Polynomial.C lcoeff) := rfl
  let E := C - Polynomial.C lcoeff * A
  by_cases hE : E = 0
  · have heq : C = Polynomial.C lcoeff * A := sub_eq_zero.mp hE
    have hmul : (c : AdjoinRoot p) = (l : AdjoinRoot p) * (a : AdjoinRoot p) := by
      rw [hc, hl, ha, heq, map_mul]
    rw [symbol_eq_mul_reduction a c l hmul]
    apply (lowDegreeSpan p).add_mem
    · exact symbol_mem_lowDegreeSpan p A (Polynomial.C lcoeff) hA hL
        (by simpa only [natDegree_C, add_zero] using hAlt) a l ha hl
    · exact symbol_neg_one_mem_lowDegreeSpan A hA hAlt a ha
  · have hEd : E.natDegree < C.natDegree :=
      natDegree_lt_natDegree hE (degree_sub_leadingRatio_mul_lt hA hC hdeg)
    let e : (AdjoinRoot p)ˣ := Units.mk0 (AdjoinRoot.mk p E)
      (AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hE (hEd.trans hClt))
    have he : (e : AdjoinRoot p) = AdjoinRoot.mk p E := rfl
    have hsub : (e : AdjoinRoot p) = (c : AdjoinRoot p) -
        (l : AdjoinRoot p) * (a : AdjoinRoot p) := by
      rw [he, hc, hl, ha]
      exact map_sub (AdjoinRoot.mk p) C (Polynomial.C lcoeff * A) |>.trans
        (congrArg (fun x => AdjoinRoot.mk p C - x) (map_mul _ _ _))
    rw [symbol_sub_mul_reduction a c l e hsub, symbol_self]
    apply (lowDegreeSpan p).add_mem
    · apply (lowDegreeSpan p).sub_mem
      · apply (lowDegreeSpan p).add_mem
        · apply (lowDegreeSpan p).sub_mem
          · exact symbol_mem_lowDegreeSpan p A E hA hE (by omega) a e ha he
          · exact symbol_mem_lowDegreeSpan p C E hC hE (by omega) c e hc he
        · exact symbol_mem_lowDegreeSpan p (Polynomial.C lcoeff) E hL hE
            (by simpa only [natDegree_C, zero_add] using hEd.trans hClt) l e hl he
      · exact symbol_mem_lowDegreeSpan p (Polynomial.C lcoeff) C hL hC
          (by simpa only [natDegree_C, zero_add] using hClt) l c hl hc
    · exact symbol_neg_one_mem_lowDegreeSpan C hC hClt c hc

end MilnorK.K2
