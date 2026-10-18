/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Symbols
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The polynomial degree filtration in every Milnor degree

The stage consists of the integer span of actual symbols with all polynomial
entries nonzero and individually smaller than the bound. These are submodules
of the original all-degree quotient, including degree zero.
-/

@[expose] public noncomputable section

namespace MilnorK

variable {F : Type*} [Field F] {r : ℕ}

/-- Inserting a unit in one coordinate is an integer-linear map. -/
def coordinateMap (a : SymbolTuple F r) (i : Fin r) : Additive Fˣ →ₗ[ℤ] K F r :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun b => symbol (Function.update a i b.toMul)
    map_zero' := symbol_update_one a i
    map_add' := fun b c => symbol_mul a i b.toMul c.toMul }

@[simp] theorem coordinateMap_apply (a : SymbolTuple F r) (i : Fin r) (b : Fˣ) :
    coordinateMap a i (Additive.ofMul b) = symbol (Function.update a i b) := rfl

/-- A spanning set of units generates every coordinate of every symbol. -/
theorem symbol_mem_of_coordinate_span (S : Submodule ℤ (K F r)) (s : Set Fˣ)
    (hbase : ∀ a : SymbolTuple F r, (∀ i, a i ∈ s) → symbol a ∈ S)
    (a : SymbolTuple F r)
    (ha : ∀ i, Additive.ofMul (a i) ∈ Submodule.span ℤ (Additive.ofMul '' s)) :
    symbol a ∈ S := by
  classical
  have h : ∀ t : Finset (Fin r), ∀ b : SymbolTuple F r,
      (∀ i ∉ t, b i ∈ s) →
      (∀ i ∈ t, Additive.ofMul (b i) ∈ Submodule.span ℤ (Additive.ofMul '' s)) →
      symbol b ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro b hb _
      exact hbase b (fun i => hb i (Finset.notMem_empty i))
    | @insert i t hit ih =>
      intro b hb hbspan
      have hspan : Submodule.span ℤ (Additive.ofMul '' s) ≤ S.comap (coordinateMap b i) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨u, hu, rfl⟩
        change symbol (Function.update b i u) ∈ S
        apply ih
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa using hu
          · simpa [Function.update_of_ne hji] using
              hb j (by simp [hj, hji])
        · intro j hj
          have hji : j ≠ i := fun e => hit (e ▸ hj)
          simpa [Function.update_of_ne hji] using hbspan j (Finset.mem_insert_of_mem hj)
      have hmem := hspan (hbspan i (Finset.mem_insert_self i t))
      simpa only [Submodule.mem_comap, coordinateMap_apply, Function.update_eq_self] using hmem
  exact h Finset.univ a (by simp) (fun i _ => ha i)

namespace DegreeFiltration

open Polynomial

variable (F : Type*) [Field F]

/-- A nonzero polynomial as its literal unit in the rational-function field. -/
def polynomialUnit (a : F[X]) (ha : a ≠ 0) : (RatFunc F)ˣ :=
  Units.mk0 (algebraMap F[X] (RatFunc F) a) (RatFunc.algebraMap_ne_zero ha)

variable {F}

@[simp] theorem polynomialUnit_coe (a : F[X]) (ha : a ≠ 0) :
    (polynomialUnit F a ha : RatFunc F) = algebraMap F[X] (RatFunc F) a := rfl

/-- Turn a tuple of nonzero polynomials into the actual tuple of rational units. -/
def polynomialTuple (a : Fin r → F[X]) (ha : ∀ i, a i ≠ 0) : SymbolTuple (RatFunc F) r :=
  fun i => polynomialUnit F (a i) (ha i)

/-- All actual polynomial symbols with individual degree smaller than `d`. -/
def lowerGenerators (F : Type*) [Field F] (r d : ℕ) : Set (K (RatFunc F) r) :=
  {x | ∃ (a : Fin r → F[X]) (ha : ∀ i, a i ≠ 0),
    (∀ i, (a i).natDegree < d) ∧ x = symbol (polynomialTuple a ha)}

/-- The true polynomial degree stage in arbitrary Milnor degree. -/
def lower (F : Type*) [Field F] (r d : ℕ) : Submodule ℤ (K (RatFunc F) r) :=
  Submodule.span ℤ (lowerGenerators F r d)

/-- Every bounded polynomial tuple gives an element of the actual stage. -/
theorem polynomial_symbol_mem_lower (d : ℕ) (a : Fin r → F[X])
    (ha : ∀ i, a i ≠ 0) (hdeg : ∀ i, (a i).natDegree < d) :
    symbol (polynomialTuple a ha) ∈ lower F r d :=
  Submodule.subset_span ⟨a, ha, hdeg, rfl⟩

/-- The polynomial degree filtration is increasing. -/
theorem lower_mono {d e : ℕ} (hde : d ≤ e) : lower F r d ≤ lower F r e := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, hdeg, rfl⟩
  exact polynomial_symbol_mem_lower e a ha (fun i => (hdeg i).trans_le hde)

/-- Multiplication of polynomial units is literal multiplication. -/
theorem polynomialUnit_mul (a b : F[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    polynomialUnit F (a * b) (mul_ne_zero ha hb) =
      polynomialUnit F a ha * polynomialUnit F b hb := by
  apply Units.ext
  exact map_mul (algebraMap F[X] (RatFunc F)) a b

@[simp] theorem polynomialUnit_one : polynomialUnit F (1 : F[X]) one_ne_zero = 1 := by
  apply Units.ext
  exact map_one (algebraMap F[X] (RatFunc F))

@[simp] theorem polynomialUnit_neg_one :
    polynomialUnit F (-1 : F[X]) (neg_ne_zero.mpr one_ne_zero) = -1 := by
  apply Units.ext
  simp only [polynomialUnit_coe, map_neg, map_one, Units.val_neg, Units.val_one]

/-- The numerator and denominator recover the original rational unit. -/
theorem polynomialUnit_num_div_denom (u : (RatFunc F)ˣ) :
    polynomialUnit F (u : RatFunc F).num (RatFunc.num_ne_zero u.ne_zero) /
      polynomialUnit F (u : RatFunc F).denom (RatFunc.denom_ne_zero _) = u := by
  apply Units.ext
  simpa only [Units.val_div_eq_div_val, polynomialUnit_coe] using
    RatFunc.num_div_denom (u : RatFunc F)

/-- Every rational symbol has a finite polynomial degree bound. -/
theorem symbol_mem_some_lower (a : SymbolTuple (RatFunc F) r) :
    ∃ d : ℕ, symbol a ∈ lower F r d := by
  classical
  let d := (Finset.univ.sup fun i =>
    max (a i : RatFunc F).num.natDegree (a i : RatFunc F).denom.natDegree) + 1
  let s : Set (RatFunc F)ˣ := {u | ∃ (p : F[X]) (hp : p ≠ 0),
    p.natDegree < d ∧ u = polynomialUnit F p hp}
  refine ⟨d, symbol_mem_of_coordinate_span (lower F r d) s ?_ a ?_⟩
  · intro b hb
    choose p hp hpd hpu using hb
    have heq : b = polynomialTuple p hp := funext hpu
    rw [heq]
    exact polynomial_symbol_mem_lower d p hp hpd
  · intro i
    have hn : (a i : RatFunc F).num.natDegree < d := by
      apply Nat.lt_succ_of_le
      exact (le_max_left _ _).trans (Finset.le_sup (f := fun i =>
        max (a i : RatFunc F).num.natDegree (a i : RatFunc F).denom.natDegree)
        (Finset.mem_univ i))
    have hd : (a i : RatFunc F).denom.natDegree < d := by
      apply Nat.lt_succ_of_le
      exact (le_max_right _ _).trans (Finset.le_sup (f := fun i =>
        max (a i : RatFunc F).num.natDegree (a i : RatFunc F).denom.natDegree)
        (Finset.mem_univ i))
    rw [← polynomialUnit_num_div_denom (a i)]
    change Additive.ofMul (polynomialUnit F (a i : RatFunc F).num
        (RatFunc.num_ne_zero (a i).ne_zero)) -
      Additive.ofMul (polynomialUnit F (a i : RatFunc F).denom (RatFunc.denom_ne_zero _)) ∈ _
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨_, ⟨_, _, hn, rfl⟩, rfl⟩
    · exact Submodule.subset_span ⟨_, ⟨_, _, hd, rfl⟩, rfl⟩

private def boundedDegreeSubmodule (F : Type*) [Field F] (r : ℕ) :
    Submodule ℤ (K (RatFunc F) r) where
  carrier := {x | ∃ d : ℕ, x ∈ lower F r d}
  zero_mem' := ⟨0, (lower F r 0).zero_mem⟩
  add_mem' := by
    rintro x y ⟨d, hd⟩ ⟨e, he⟩
    exact ⟨max d e, (lower F r (max d e)).add_mem
      (lower_mono (le_max_left d e) hd) (lower_mono (le_max_right d e) he)⟩
  smul_mem' := by
    rintro z x ⟨d, hd⟩
    exact ⟨d, (lower F r d).smul_mem z hd⟩

/-- Every class of the actual rational-function Milnor group lies in a finite stage. -/
theorem exists_mem_lower (x : K (RatFunc F) r) : ∃ d : ℕ, x ∈ lower F r d := by
  have h : (boundedDegreeSubmodule F r).mkQ = 0 := by
    apply linearMap_ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr (symbol_mem_some_lower a)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

/-- The actual finite stages exhaust the entire all-degree quotient. -/
theorem iSup_lower_eq_top : (⨆ d : ℕ, lower F r d) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨d, hd⟩ := exists_mem_lower x
  exact (show lower F r d ≤ ⨆ e : ℕ, lower F r e from le_iSup (lower F r) d) hd

/-- Constant polynomial units are the units induced by the constant field map. -/
theorem polynomialUnit_constant (a : Fˣ) :
    polynomialUnit F (C (a : F)) (C_ne_zero.mpr a.ne_zero) =
      Units.map (RatFunc.C : F →+* RatFunc F).toMonoidHom a := by
  apply Units.ext
  exact RatFunc.algebraMap_C (a : F)

/-- The degree-one stage is exactly the constant-field image, in every Milnor degree. -/
theorem lower_one_eq_constant_range :
    lower F r 1 = LinearMap.range (MilnorK.map r (RatFunc.C : F →+* RatFunc F)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, hdeg, rfl⟩
    have hc : ∀ i, ∃ c : F, C c = a i := fun i =>
      natDegree_eq_zero.mp (Nat.lt_one_iff.mp (hdeg i))
    choose c hc using hc
    let u : SymbolTuple F r := fun i => Units.mk0 (c i) (by
      intro hz
      exact ha i (by rw [← hc i, hz, map_zero]))
    refine ⟨symbol u, ?_⟩
    rw [MilnorK.map_symbol]
    congr 1
    funext i
    change Units.map RatFunc.C.toMonoidHom (u i) = polynomialUnit F (a i) (ha i)
    rw [← polynomialUnit_constant]
    congr 1
    exact hc i
  · have h : (lower F r 1).mkQ.comp (MilnorK.map r (RatFunc.C : F →+* RatFunc F)) = 0 := by
      apply linearMap_ext
      intro a
      rw [LinearMap.comp_apply, MilnorK.map_symbol]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have heq : (Units.map (RatFunc.C : F →+* RatFunc F).toMonoidHom) ∘ a =
          polynomialTuple (fun i => C (a i : F)) (fun i => C_ne_zero.mpr (a i).ne_zero) := by
        funext i
        exact (polynomialUnit_constant (a i)).symm
      rw [heq]
      exact polynomial_symbol_mem_lower 1 _ _ (by simp)
    rintro x ⟨y, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h y)

variable (p : F[X]) [Fact (Irreducible p)]

/-- The remainder of a product of nonzero reduced representatives is nonzero. -/
theorem reduced_mul_ne_zero (hp : p.Monic) (a a' : F[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree) :
    (a * a') %ₘ p ≠ 0 := by
  intro hzero
  have hdvd := (modByMonic_eq_zero_iff_dvd hp).mp hzero
  rcases (Fact.out : Irreducible p).prime.dvd_mul.mp hdvd with hpa | hpa'
  · exact hp.not_dvd_of_natDegree_lt ha hadeg hpa
  · exact hp.not_dvd_of_natDegree_lt ha' ha'deg hpa'

/-- The product remainder has genuinely smaller degree than the irreducible modulus. -/
theorem reduced_mul_natDegree_lt (hp : p.Monic) (a a' : F[X]) :
    ((a * a') %ₘ p).natDegree < p.natDegree :=
  natDegree_modByMonic_lt (a * a') hp (Fact.out : Irreducible p).ne_one

omit [Fact (Irreducible p)] in
/-- In the nontrivial branch monic division supplies a nonzero smaller-degree correction. -/
theorem reduced_mul_correction (hp : p.Monic) (a a' : F[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree)
    (hne : a * a' ≠ (a * a') %ₘ p) :
    ∃ f : F[X], f ≠ 0 ∧ f.natDegree < p.natDegree ∧
      (a * a') %ₘ p = a * a' + f * p := by
  refine ⟨-((a * a') /ₘ p), ?_, ?_, ?_⟩
  · intro hf
    have hdiv := neg_eq_zero.mp hf
    have heq := modByMonic_add_div (a * a') p
    rw [hdiv, mul_zero, add_zero] at heq
    exact hne heq.symm
  · rw [natDegree_neg, natDegree_divByMonic _ hp, natDegree_mul ha ha']
    omega
  · have heq := modByMonic_add_div (a * a') p
    calc
      (a * a') %ₘ p = a * a' - p * ((a * a') /ₘ p) := eq_sub_of_add_eq heq
      _ = a * a' + -((a * a') /ₘ p) * p := by ring

/-- Reduced representatives summing to one in the residue field already sum to one literally. -/
theorem reduced_add_eq_one (hp : p.Monic) (a b : F[X])
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hsum : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) : a + b = 1 := by
  have hzero : AdjoinRoot.mk p (a + b - 1) = 0 := by
    rw [map_sub, map_add, map_one, hsum, sub_self]
  have hdeg : (a + b - 1).natDegree < p.natDegree := by
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · exact (natDegree_add_le _ _).trans_lt (max_lt hadeg hbdeg)
    · simpa only [natDegree_one] using (Nat.zero_le a.natDegree).trans_lt hadeg
  by_contra hne
  exact hp.not_dvd_of_natDegree_lt (sub_ne_zero.mpr hne) hdeg
    (AdjoinRoot.mk_eq_zero.mp hzero)

end DegreeFiltration
end MilnorK
