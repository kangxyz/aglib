/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DegreeFiltration
public import Aglib.KTheory.MilnorK.K3.ResidueSupport
public import Aglib.KTheory.MilnorK.K3.Map
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Generation of the actual polynomial degree stages

Normalized polynomial factorization retains the leading coefficient. Two monic
factors of the top degree are reduced using their smaller-degree difference,
with the Euclidean sign term retained. Repeated factors use the self-sign law.
These are identities in the original rational-function Milnor K₃ quotient.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DegreeFiltration

open Polynomial PolynomialResidue

variable {k : Type*} [Field k]

/-- The symbols with one monic irreducible of degree `d` and two smaller entries. -/
def topGenerators (k : Type*) [Field k] (d : ℕ) : Set (Group (RatFunc k)) :=
  {x | ∃ (p a b : k[X]) (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0),
    p.Monic ∧ Irreducible p ∧ p.natDegree = d ∧
    a.natDegree < d ∧ b.natDegree < d ∧
    x = symbol3 (polynomialUnit p hp) (polynomialUnit a ha) (polynomialUnit b hb)}

/-- The proposed decomposition of one actual degree stage. -/
def generatedStage (k : Type*) [Field k] (d : ℕ) : Submodule ℤ (Group (RatFunc k)) :=
  lower k d ⊔ Submodule.span ℤ (topGenerators k d)

private theorem polynomialUnit_mul (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    polynomialUnit (a * b) (mul_ne_zero ha hb) =
      polynomialUnit a ha * polynomialUnit b hb := by
  apply Units.ext
  exact map_mul (algebraMap k[X] (RatFunc k)) a b

private theorem polynomialUnit_one : polynomialUnit (1 : k[X]) one_ne_zero = 1 := by
  apply Units.ext
  exact map_one (algebraMap k[X] (RatFunc k))

private theorem polynomialUnit_neg_one :
    polynomialUnit (-1 : k[X]) (neg_ne_zero.mpr one_ne_zero) = -1 := by
  apply Units.ext
  simp only [polynomialUnit_coe, map_neg, map_one, Units.val_neg, Units.val_one]

private theorem top_mem (d : ℕ) (p a b : k[X])
    (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpm : p.Monic) (hpi : Irreducible p) (hpdeg : p.natDegree = d)
    (hadeg : a.natDegree < d) (hbdeg : b.natDegree < d) :
    symbol3 (polynomialUnit p hp) (polynomialUnit a ha) (polynomialUnit b hb) ∈
      generatedStage k d :=
  (show Submodule.span ℤ (topGenerators k d) ≤ generatedStage k d from le_sup_right)
    (Submodule.subset_span
    ⟨p, a, b, hp, ha, hb, hpm, hpi, hpdeg, hadeg, hbdeg, rfl⟩)

/-- Reduction of two monic top-degree entries, retaining the exact sign correction. -/
private theorem reduce_top_pair (d : ℕ) (hd : 0 < d)
    (S : Submodule ℤ (Group (RatFunc k))) (p q : k[X])
    (hp : p.Monic) (hq : q.Monic) (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d)
    (c : (RatFunc k)ˣ)
    (hpsmall : ∀ (r : k[X]) (hr : r ≠ 0), r.natDegree < d →
      symbol3 (polynomialUnit p hp.ne_zero) (polynomialUnit r hr) c ∈ S)
    (hqsmall : ∀ (r : k[X]) (hr : r ≠ 0), r.natDegree < d →
      symbol3 (polynomialUnit q hq.ne_zero) (polynomialUnit r hr) c ∈ S) :
    symbol3 (polynomialUnit p hp.ne_zero) (polynomialUnit q hq.ne_zero) c ∈ S := by
  have hsign : symbol3 (polynomialUnit q hq.ne_zero) (-1) c ∈ S := by
    rw [← polynomialUnit_neg_one]
    exact hqsmall (-1) (neg_ne_zero.mpr one_ne_zero) (by simpa using hd)
  by_cases heq : p = q
  · subst q
    rw [symbol3_self_left]
    exact hsign
  · have hr : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
    have hrdeg : (q - p).natDegree < d :=
      by
        have hdegrees : q.degree = p.degree := by
          rw [degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hp.ne_zero, hpdeg, hqdeg]
        have hlt := degree_sub_lt_left hdegrees hq.ne_zero (hq.trans hp.symm)
        rw [← hqdeg]
        exact natDegree_lt_natDegree hr hlt
    have hsum : (polynomialUnit p hp.ne_zero : RatFunc k) +
        (polynomialUnit (q - p) hr : RatFunc k) = polynomialUnit q hq.ne_zero := by
      simp only [polynomialUnit_coe, map_sub]
      ring
    rw [symbol3_euclidean _ _ _ _ hsum]
    exact S.add_mem (S.sub_mem (hpsmall _ hr hrdeg) (hqsmall _ hr hrdeg)) hsign

private theorem two_top_small (d : ℕ) (hd : 0 < d) (p q a : k[X])
    (hp : p.Monic) (hq : q.Monic) (hpi : Irreducible p) (hqi : Irreducible q)
    (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d)
    (ha : a ≠ 0) (hadeg : a.natDegree < d) :
    symbol3 (polynomialUnit p hp.ne_zero) (polynomialUnit q hq.ne_zero)
      (polynomialUnit a ha) ∈ generatedStage k d := by
  apply reduce_top_pair d hd (generatedStage k d) p q hp hq hpdeg hqdeg
  · intro r hr hrdeg
    exact top_mem d p r a hp.ne_zero hr ha hp hpi hpdeg hrdeg hadeg
  · intro r hr hrdeg
    exact top_mem d q r a hq.ne_zero hr ha hq hqi hqdeg hrdeg hadeg

private theorem three_top (d : ℕ) (hd : 0 < d) (p q r : k[X])
    (hp : p.Monic) (hq : q.Monic) (hr : r.Monic)
    (hpi : Irreducible p) (hqi : Irreducible q) (hri : Irreducible r)
    (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d) (hrdeg : r.natDegree = d) :
    symbol3 (polynomialUnit p hp.ne_zero) (polynomialUnit q hq.ne_zero)
      (polynomialUnit r hr.ne_zero) ∈ generatedStage k d := by
  apply reduce_top_pair d hd (generatedStage k d) p q hp hq hpdeg hqdeg
  · intro a ha hadeg
    rw [symbol3_skew_right]
    exact (generatedStage k d).neg_mem
      (two_top_small d hd p r a hp hr hpi hri hpdeg hrdeg ha hadeg)
  · intro a ha hadeg
    rw [symbol3_skew_right]
    exact (generatedStage k d).neg_mem
      (two_top_small d hd q r a hq hr hqi hri hqdeg hrdeg ha hadeg)

private theorem polynomialUnit_prod_property (P : (RatFunc k)ˣ → Prop)
    (hone : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (s : Multiset k[X]) (hs : ∀ a ∈ s, a ≠ 0)
    (hP : ∀ (a : k[X]) (ha : a ∈ s), P (polynomialUnit a (hs a ha))) :
    P (polynomialUnit s.prod (Multiset.prod_ne_zero (fun h => hs 0 h rfl))) := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.prod_zero, polynomialUnit_one] using hone
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have hP' : ∀ (b : k[X]) (hb : b ∈ s), P (polynomialUnit b (hs' b hb)) :=
      fun b hb => hP b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.prod_cons]
    change P (polynomialUnit (a * s.prod)
      (mul_ne_zero ha (Multiset.prod_ne_zero (fun h => hs' 0 h rfl))))
    rw [polynomialUnit_mul]
    exact hmul (polynomialUnit a ha)
      (polynomialUnit s.prod (Multiset.prod_ne_zero (fun h => hs' 0 h rfl)))
        (hP a (Multiset.mem_cons_self a s)) (ih hs' hP')

/-- Literal normalized factorization reduces multiplicative predicates to smaller
polynomials and monic irreducibles of the top degree. The constant is retained. -/
private theorem normalized_factor_induction (d : ℕ) (hd : 0 < d)
    (P : (RatFunc k)ˣ → Prop) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (hsmall : ∀ (a : k[X]) (ha : a ≠ 0), a.natDegree < d → P (polynomialUnit a ha))
    (htop : ∀ (p : k[X]) (hp : p.Monic), Irreducible p → p.natDegree = d →
      P (polynomialUnit p hp.ne_zero))
    (a : k[X]) (ha : a ≠ 0) (hadeg : a.natDegree ≤ d) : P (polynomialUnit a ha) := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors a
  have hs : ∀ p ∈ s, p ≠ 0 := by
    intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff ha).mp hp).1.ne_zero
  have hP : ∀ (p : k[X]) (hp : p ∈ s), P (polynomialUnit p (hs p hp)) := by
    intro p hp
    obtain ⟨hpi, hpm, hpdvd⟩ := (Polynomial.mem_normalizedFactors_iff ha).mp hp
    have hpdeg := (Polynomial.natDegree_le_of_dvd hpdvd ha).trans hadeg
    rcases lt_or_eq_of_le hpdeg with hlt | heq
    · exact hsmall p hpi.ne_zero hlt
    · exact htop p hpm hpi heq
  have hlc : C a.leadingCoeff ≠ 0 := C_ne_zero.mpr (leadingCoeff_ne_zero.mpr ha)
  have hc := hsmall (C a.leadingCoeff) hlc (by simpa only [natDegree_C] using hd)
  have hprod := polynomialUnit_prod_property P hone hmul s hs hP
  have hfactor := Polynomial.leadingCoeff_mul_prod_normalizedFactors a
  have hunits : polynomialUnit a ha = polynomialUnit (C a.leadingCoeff) hlc *
      polynomialUnit s.prod (Multiset.prod_ne_zero (fun h => hs 0 h rfl)) := by
    rw [← polynomialUnit_mul]
    congr 1
    exact hfactor.symm
  rw [hunits]
  exact hmul _ _ hc hprod

private def degreeAtom (d : ℕ) (a : k[X]) : Prop :=
  a.natDegree < d ∨ (a.Monic ∧ Irreducible a ∧ a.natDegree = d)

private theorem atomic_triple_mem (d : ℕ) (hd : 0 < d) (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (haatom : degreeAtom d a) (hbatom : degreeAtom d b) (hcatom : degreeAtom d c) :
    symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
      generatedStage k d := by
  rcases haatom with hadeg | ⟨ham, hai, hadeg⟩ <;>
    rcases hbatom with hbdeg | ⟨hbm, hbi, hbdeg⟩ <;>
    rcases hcatom with hcdeg | ⟨hcm, hci, hcdeg⟩
  · exact (show lower k d ≤ generatedStage k d from le_sup_left)
      (polynomial_symbol_mem_lower d a b c ha hb hc hadeg hbdeg hcdeg)
  · rw [symbol3_cyclic]
    exact top_mem d c a b hc ha hb hcm hci hcdeg hadeg hbdeg
  · rw [symbol3_cyclic_left]
    exact top_mem d b c a hb hc ha hbm hbi hbdeg hcdeg hadeg
  · rw [symbol3_cyclic_left]
    exact two_top_small d hd b c a hbm hcm hbi hci hbdeg hcdeg ha hadeg
  · exact top_mem d a b c ha hb hc ham hai hadeg hbdeg hcdeg
  · rw [symbol3_skew_right]
    exact (generatedStage k d).neg_mem
      (two_top_small d hd a c b ham hcm hai hci hadeg hcdeg hb hbdeg)
  · exact two_top_small d hd a b c ham hbm hai hbi hadeg hbdeg hc hcdeg
  · exact three_top d hd a b c ham hbm hcm hai hbi hci hadeg hbdeg hcdeg

/-- Every polynomial triple bounded by `d` is generated by the lower stage
and actual one-top-irreducible symbols. -/
theorem polynomial_symbol_mem_generatedStage (d : ℕ) (hd : 0 < d) (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hadeg : a.natDegree ≤ d) (hbdeg : b.natDegree ≤ d) (hcdeg : c.natDegree ≤ d) :
    symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
      generatedStage k d := by
  have hlast : ∀ (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0),
      degreeAtom d a → degreeAtom d b →
      symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
        generatedStage k d := by
    intro a b ha hb haa hba
    apply normalized_factor_induction d hd
      (fun u => symbol3 (polynomialUnit a ha) (polynomialUnit b hb) u ∈ generatedStage k d)
      (by simp) ?_ ?_ ?_ c hc hcdeg
    · intro u v hu hv
      rw [symbol3_mul_right]
      exact (generatedStage k d).add_mem hu hv
    · intro r hr hrdeg
      exact atomic_triple_mem d hd a b r ha hb hr haa hba (Or.inl hrdeg)
    · intro p hp hpi hpdeg
      exact atomic_triple_mem d hd a b p ha hb hp.ne_zero haa hba
        (Or.inr ⟨hp, hpi, hpdeg⟩)
  have hmiddle : ∀ (a : k[X]) (ha : a ≠ 0), degreeAtom d a →
      symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
        generatedStage k d := by
    intro a ha haa
    apply normalized_factor_induction d hd
      (fun u => symbol3 (polynomialUnit a ha) u (polynomialUnit c hc) ∈ generatedStage k d)
      (by simp) ?_ ?_ ?_ b hb hbdeg
    · intro u v hu hv
      rw [symbol3_mul_middle]
      exact (generatedStage k d).add_mem hu hv
    · intro r hr hrdeg
      exact hlast a r ha hr haa (Or.inl hrdeg)
    · intro p hp hpi hpdeg
      exact hlast a p ha hp.ne_zero haa (Or.inr ⟨hp, hpi, hpdeg⟩)
  apply normalized_factor_induction d hd
    (fun u => symbol3 u (polynomialUnit b hb) (polynomialUnit c hc) ∈ generatedStage k d)
    (by simp) ?_ ?_ ?_ a ha hadeg
  · intro u v hu hv
    rw [symbol3_mul_left]
    exact (generatedStage k d).add_mem hu hv
  · intro r hr hrdeg
    exact hmiddle r hr (Or.inl hrdeg)
  · intro p hp hpi hpdeg
    exact hmiddle p hp.ne_zero (Or.inr ⟨hp, hpi, hpdeg⟩)

/-- The next actual degree stage consists exactly of the preceding stage and
symbols with one monic irreducible of degree `d` and two smaller entries. -/
theorem lower_succ_eq (d : ℕ) (hd : 0 < d) :
    lower k (d + 1) = lower k d ⊔ Submodule.span ℤ (topGenerators k d) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, b, c, ha, hb, hc, hadeg, hbdeg, hcdeg, rfl⟩
    exact polynomial_symbol_mem_generatedStage d hd a b c ha hb hc
      (Nat.lt_succ_iff.mp hadeg) (Nat.lt_succ_iff.mp hbdeg) (Nat.lt_succ_iff.mp hcdeg)
  · apply sup_le (lower_mono (Nat.le_succ d))
    apply Submodule.span_le.mpr
    rintro x ⟨p, a, b, hp, ha, hb, _, _, hpdeg, hadeg, hbdeg, rfl⟩
    exact polynomial_symbol_mem_lower (d + 1) p a b hp ha hb
      (by omega) (by omega) (by omega)

/-- Every actual rational-function symbol belongs to a finite degree stage. -/
theorem symbol_mem_some_lower (a b c : (RatFunc k)ˣ) :
    ∃ d : ℕ, symbol3 a b c ∈ lower k d := by
  let d := (a : RatFunc k).num.natDegree + (a : RatFunc k).denom.natDegree +
    (b : RatFunc k).num.natDegree + (b : RatFunc k).denom.natDegree +
    (c : RatFunc k).num.natDegree + (c : RatFunc k).denom.natDegree + 1
  refine ⟨d, ?_⟩
  rw [← polynomialUnit_num_div_denom a, ← polynomialUnit_num_div_denom b,
    ← polynomialUnit_num_div_denom c]
  simp only [symbol3_div_left, symbol3_div_middle, symbol3_div_right]
  repeat' apply (lower k d).sub_mem
  all_goals
    apply polynomial_symbol_mem_lower <;> dsimp [d] <;> omega

private def boundedDegreeSubmodule (k : Type*) [Field k] : Submodule ℤ (Group (RatFunc k)) where
  carrier := {x | ∃ d : ℕ, x ∈ lower k d}
  zero_mem' := ⟨0, (lower k 0).zero_mem⟩
  add_mem' := by
    rintro x y ⟨d, hd⟩ ⟨e, he⟩
    exact ⟨max d e, (lower k (max d e)).add_mem
      (lower_mono (le_max_left d e) hd) (lower_mono (le_max_right d e) he)⟩
  smul_mem' := by
    rintro n x ⟨d, hd⟩
    exact ⟨d, (lower k d).smul_mem n hd⟩

/-- The actual degree filtration exhausts every class of rational-function Milnor K₃. -/
theorem exists_mem_lower (x : Group (RatFunc k)) : ∃ d : ℕ, x ∈ lower k d := by
  have h : (boundedDegreeSubmodule k).mkQ = 0 := by
    apply MilnorK.K3.linearMap_ext
    intro a b c
    exact (Submodule.Quotient.mk_eq_zero _).mpr (symbol_mem_some_lower a b c)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

/-- Equivalently, the supremum of the actual finite stages is the whole K₃ group. -/
theorem iSup_lower_eq_top : (⨆ d : ℕ, lower k d) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨d, hd⟩ := exists_mem_lower x
  exact (show lower k d ≤ ⨆ e : ℕ, lower k e from le_iSup (lower k) d) hd

private theorem polynomialUnit_constant (a : kˣ) :
    polynomialUnit (C (a : k)) (C_ne_zero.mpr a.ne_zero) =
      Units.map (RatFunc.C : k →+* RatFunc k).toMonoidHom a := by
  apply Units.ext
  exact RatFunc.algebraMap_C (a : k)

/-- The first actual degree stage is exactly the image of constant Milnor K₃. -/
theorem lower_one_eq_constant_range :
    lower k 1 = LinearMap.range (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, b, c, ha, hb, hc, hadeg, hbdeg, hcdeg, rfl⟩
    obtain ⟨a', rfl⟩ := natDegree_eq_zero.mp (Nat.lt_one_iff.mp hadeg)
    obtain ⟨b', rfl⟩ := natDegree_eq_zero.mp (Nat.lt_one_iff.mp hbdeg)
    obtain ⟨c', rfl⟩ := natDegree_eq_zero.mp (Nat.lt_one_iff.mp hcdeg)
    refine ⟨symbol3 (Units.mk0 a' (C_ne_zero.mp ha))
      (Units.mk0 b' (C_ne_zero.mp hb)) (Units.mk0 c' (C_ne_zero.mp hc)), ?_⟩
    rw [MilnorK.K3.map_symbol3, ← polynomialUnit_constant, ← polynomialUnit_constant,
      ← polynomialUnit_constant]
    rfl
  · have h : (lower k 1).mkQ.comp (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)) = 0 := by
      apply MilnorK.K3.linearMap_ext
      intro a b c
      rw [LinearMap.comp_apply, MilnorK.K3.map_symbol3,
        ← polynomialUnit_constant, ← polynomialUnit_constant, ← polynomialUnit_constant]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (polynomial_symbol_mem_lower 1 (C (a : k)) (C (b : k)) (C (c : k))
          (C_ne_zero.mpr a.ne_zero) (C_ne_zero.mpr b.ne_zero) (C_ne_zero.mpr c.ne_zero)
          (by simp) (by simp) (by simp))
    rintro x ⟨y, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h y)

end MilnorK.K3.DegreeFiltration
