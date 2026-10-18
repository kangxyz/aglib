/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.DegreeFiltration
public import Aglib.KTheory.MilnorK.TupleSymbols

/-!
# Polynomial generation in arbitrary Milnor degree

Top symbols place their unique degree-`d` monic irreducible in the final
coordinate. Every other entry is individually smaller than `d`. Normalized
factorization retains its leading coefficient.
-/

@[expose] public noncomputable section

namespace MilnorK.DegreeFiltration

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- Symbols with the degree-`d` irreducible in their final coordinate. -/
def topGenerators (F : Type*) [Field F] (n d : ℕ) : Set (K (RatFunc F) (n + 1)) :=
  {x | ∃ (p : F[X]) (a : Fin n → F[X]) (hp : p ≠ 0) (ha : ∀ i, a i ≠ 0),
    p.Monic ∧ Irreducible p ∧ p.natDegree = d ∧
    (∀ i, (a i).natDegree < d) ∧
    x = symbol (Fin.snoc (polynomialTuple a ha) (polynomialUnit F p hp))}

/-- The lower stage together with the final-slot top generators. -/
def generatedStage (F : Type*) [Field F] (n d : ℕ) :
    Submodule ℤ (K (RatFunc F) (n + 1)) :=
  lower F (n + 1) d ⊔ Submodule.span ℤ (topGenerators F n d)

/-- A final-slot top symbol is in the generated stage by its actual witnesses. -/
theorem top_mem (d : ℕ) (p : F[X]) (a : Fin n → F[X])
    (hp : p ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hpm : p.Monic) (hpi : Irreducible p) (hpdeg : p.natDegree = d)
    (hadeg : ∀ i, (a i).natDegree < d) :
    symbol (Fin.snoc (polynomialTuple a ha) (polynomialUnit F p hp)) ∈
      generatedStage F n d :=
  (show Submodule.span ℤ (topGenerators F n d) ≤ generatedStage F n d from le_sup_right)
    (Submodule.subset_span ⟨p, a, hp, ha, hpm, hpi, hpdeg, hadeg, rfl⟩)

private theorem polynomialUnit_prod_property (P : (RatFunc F)ˣ → Prop)
    (hone : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (s : Multiset F[X]) (hs : ∀ a ∈ s, a ≠ 0)
    (hP : ∀ (a : F[X]) (ha : a ∈ s), P (polynomialUnit F a (hs a ha))) :
    P (polynomialUnit F s.prod (Multiset.prod_ne_zero (fun h => hs 0 h rfl))) := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.prod_zero, polynomialUnit_one] using hone
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have hP' : ∀ (b : F[X]) (hb : b ∈ s), P (polynomialUnit F b (hs' b hb)) :=
      fun b hb => hP b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.prod_cons]
    change P (polynomialUnit F (a * s.prod)
      (mul_ne_zero ha (Multiset.prod_ne_zero (fun h => hs' 0 h rfl))))
    rw [polynomialUnit_mul]
    exact hmul (polynomialUnit F a ha)
      (polynomialUnit F s.prod (Multiset.prod_ne_zero (fun h => hs' 0 h rfl)))
        (hP a (Multiset.mem_cons_self a s)) (ih hs' hP')

/-- Normalized polynomial factorization, with the leading coefficient retained. -/
theorem normalized_factor_induction (d : ℕ) (hd : 0 < d)
    (P : (RatFunc F)ˣ → Prop) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (hsmall : ∀ (a : F[X]) (ha : a ≠ 0), a.natDegree < d → P (polynomialUnit F a ha))
    (htop : ∀ (p : F[X]) (hp : p.Monic), Irreducible p → p.natDegree = d →
      P (polynomialUnit F p hp.ne_zero))
    (a : F[X]) (ha : a ≠ 0) (hadeg : a.natDegree ≤ d) : P (polynomialUnit F a ha) := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors a
  have hs : ∀ p ∈ s, p ≠ 0 := by
    intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff ha).mp hp).1.ne_zero
  have hP : ∀ (p : F[X]) (hp : p ∈ s), P (polynomialUnit F p (hs p hp)) := by
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
  have hunits : polynomialUnit F a ha = polynomialUnit F (C a.leadingCoeff) hlc *
      polynomialUnit F s.prod (Multiset.prod_ne_zero (fun h => hs 0 h rfl)) := by
    rw [← polynomialUnit_mul]
    congr 1
    exact hfactor.symm
  rw [hunits]
  exact hmul _ _ hc hprod

/-- The polynomial atoms used by normalized factorization. -/
def degreeAtom (d : ℕ) (a : F[X]) : Prop :=
  a.natDegree < d ∨ (a.Monic ∧ Irreducible a ∧ a.natDegree = d)

/-- Replacing one nonzero entry by another preserves coordinatewise nonvanishing. -/
theorem update_nonzero {r : ℕ} (a : Fin r → F[X]) (ha : ∀ i, a i ≠ 0)
    (i : Fin r) (b : F[X]) (hb : b ≠ 0) :
    ∀ j, Function.update a i b j ≠ 0 := by
  classical
  intro j
  by_cases h : j = i
  · subst j
    simpa using hb
  · simpa [h] using ha j

/-- Polynomial tuples commute literally with replacement in one coordinate. -/
theorem polynomialTuple_update {r : ℕ} (a : Fin r → F[X]) (ha : ∀ i, a i ≠ 0)
    (i : Fin r) (b : F[X]) (hb : b ≠ 0) :
    polynomialTuple (Function.update a i b) (update_nonzero a ha i b hb) =
      Function.update (polynomialTuple a ha) i (polynomialUnit F b hb) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [polynomialTuple]
  · simp [polynomialTuple, h]

/-- A polynomial tuple whose only possible top entry is already last lies in the stage. -/
theorem polynomial_symbol_mem_generatedStage_last (d : ℕ)
    (a : Fin (n + 1) → F[X]) (ha : ∀ i, a i ≠ 0)
    (hm : (a (Fin.last n)).Monic) (hi : Irreducible (a (Fin.last n)))
    (hd : (a (Fin.last n)).natDegree = d)
    (hsmall : ∀ i : Fin n, (a i.castSucc).natDegree < d) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d := by
  have h := top_mem d (a (Fin.last n)) (fun i : Fin n => a i.castSucc)
    (ha (Fin.last n)) (fun i => ha i.castSucc) hm hi hd hsmall
  have heq : Fin.snoc (polynomialTuple (fun i : Fin n => a i.castSucc)
      (fun i => ha i.castSucc)) (polynomialUnit F (a (Fin.last n)) (ha (Fin.last n))) =
      polynomialTuple a ha := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [polynomialTuple]
  rwa [heq] at h

/-- An arbitrary position for the single top entry gives the same generated submodule. -/
theorem polynomial_symbol_mem_generatedStage_one_top (d : ℕ)
    (a : Fin (n + 1) → F[X]) (ha : ∀ i, a i ≠ 0) (i : Fin (n + 1))
    (hm : (a i).Monic) (hi : Irreducible (a i)) (hd : (a i).natDegree = d)
    (hsmall : ∀ j, j ≠ i → (a j).natDegree < d) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d := by
  classical
  by_cases hil : i = Fin.last n
  · subst i
    exact polynomial_symbol_mem_generatedStage_last d a ha hm hi hd
      (fun j => hsmall j.castSucc (Fin.castSucc_ne_last j))
  · let b := Function.update (Function.update a i (a (Fin.last n))) (Fin.last n) (a i)
    have hb : ∀ j, b j ≠ 0 :=
      update_nonzero _ (update_nonzero a ha i _ (ha (Fin.last n))) _ _ (ha i)
    have hbmem : symbol (polynomialTuple b hb) ∈ generatedStage F n d := by
      apply polynomial_symbol_mem_generatedStage_last d b hb
      · simpa [b] using hm
      · simpa [b] using hi
      · simpa [b] using hd
      · intro j
        by_cases hji : j.castSucc = i
        · simpa [b, hji, hil] using hsmall (Fin.last n) (Ne.symm hil)
        · simpa [b, Fin.castSucc_ne_last j, hji] using hsmall j.castSucc hji
    have hsk := symbol_skew (polynomialTuple a ha) i (Fin.last n) hil
    have heq : polynomialTuple b hb = Function.update
        (Function.update (polynomialTuple a ha) i (polynomialTuple a ha (Fin.last n)))
        (Fin.last n) (polynomialTuple a ha i) := by
      funext j
      by_cases hjl : j = Fin.last n
      · subst j
        simp [polynomialTuple, b]
      · by_cases hji : j = i
        · subst j
          simp [polynomialTuple, b, hil]
        · simp [polynomialTuple, b, hjl, hji]
    rw [← heq] at hsk
    rw [hsk]
    exact (generatedStage F n d).neg_mem hbmem

private theorem pair_euclidean {E : Type*} [Field E] (p q r : Eˣ)
    (h : (p : E) + (r : E) = q) :
    MilnorK.K2.symbol p q = MilnorK.K2.symbol p r - MilnorK.K2.symbol q r +
      MilnorK.K2.symbol q (-1) := by
  have hsum : ((p / q : Eˣ) : E) + ((r / q : Eˣ) : E) = 1 := by
    simp only [Units.val_div_eq_div_val]
    rw [← add_div, h, div_self q.ne_zero]
  have hs := MilnorK.K2.steinberg (p / q) (r / q) hsum
  rw [MilnorK.K2.symbol_div_left, MilnorK.K2.symbol_div_right,
    MilnorK.K2.symbol_div_right, MilnorK.K2.symbol_self] at hs
  calc
    MilnorK.K2.symbol p q = (MilnorK.K2.symbol p r - MilnorK.K2.symbol q r +
        MilnorK.K2.symbol q (-1)) - ((MilnorK.K2.symbol p r - MilnorK.K2.symbol p q) -
        (MilnorK.K2.symbol q r - MilnorK.K2.symbol q (-1))) := by abel
    _ = _ := by rw [hs, sub_zero]

private theorem reduce_top_pair {r : ℕ} (d : ℕ) (hd : 0 < d)
    (S : Submodule ℤ (K (RatFunc F) r)) (a : SymbolTuple (RatFunc F) r)
    (i j : Fin r) (hij : i ≠ j) (p q : F[X])
    (hp : p.Monic) (hq : q.Monic) (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d)
    (hpsmall : ∀ (b : F[X]) (hb : b ≠ 0), b.natDegree < d →
      symbol (Function.update (Function.update a i (polynomialUnit F p hp.ne_zero))
        j (polynomialUnit F b hb)) ∈ S)
    (hqsmall : ∀ (b : F[X]) (hb : b ≠ 0), b.natDegree < d →
      symbol (Function.update (Function.update a i (polynomialUnit F q hq.ne_zero))
        j (polynomialUnit F b hb)) ∈ S) :
    symbol (Function.update (Function.update a i (polynomialUnit F p hp.ne_zero))
      j (polynomialUnit F q hq.ne_zero)) ∈ S := by
  have hsign : symbol (Function.update
      (Function.update a i (polynomialUnit F q hq.ne_zero)) j (-1)) ∈ S := by
    rw [← polynomialUnit_neg_one]
    exact hqsmall (-1) (neg_ne_zero.mpr one_ne_zero) (by simpa using hd)
  by_cases heq : p = q
  · subst q
    have hs := congrArg (pairMap a i j hij)
      (MilnorK.K2.symbol_self (polynomialUnit F p hp.ne_zero))
    simp only [pairMap_symbol] at hs
    rw [hs]
    exact hsign
  · have hr : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
    have hrdeg : (q - p).natDegree < d := by
      have hdegrees : q.degree = p.degree := by
        rw [degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hp.ne_zero, hpdeg, hqdeg]
      have hlt := degree_sub_lt_left hdegrees hq.ne_zero (hq.trans hp.symm)
      rw [← hqdeg]
      exact natDegree_lt_natDegree hr hlt
    have hsum : (polynomialUnit F p hp.ne_zero : RatFunc F) +
        (polynomialUnit F (q - p) hr : RatFunc F) = polynomialUnit F q hq.ne_zero := by
      simp only [polynomialUnit_coe, map_sub]
      ring
    have hs := congrArg (pairMap a i j hij) (pair_euclidean _ _ _ hsum)
    simp only [pairMap_symbol, map_add, map_sub] at hs
    rw [hs]
    exact S.add_mem (S.sub_mem (hpsmall _ hr hrdeg) (hqsmall _ hr hrdeg)) hsign

private theorem atomic_tuple_mem_topSet (d : ℕ) (hd : 0 < d)
    (t : Finset (Fin (n + 1))) (a : Fin (n + 1) → F[X])
    (ha : ∀ i, a i ≠ 0)
    (htop : ∀ i ∈ t, (a i).Monic ∧ Irreducible (a i) ∧ (a i).natDegree = d)
    (hsmall : ∀ i ∉ t, (a i).natDegree < d) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d := by
  classical
  induction t using Finset.strongInductionOn generalizing a with
  | _ t ih =>
    by_cases ht : t.Nonempty
    · obtain ⟨i, hit⟩ := ht
      obtain ⟨hmi, hii, hdi⟩ := htop i hit
      by_cases ht' : (t.erase i).Nonempty
      · obtain ⟨j, hj⟩ := ht'
        obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
        have hij := Ne.symm hji
        obtain ⟨hmj, hijj, hdj⟩ := htop j hjt
        have hreduce (p b : F[X]) (hp : p ≠ 0) (hb : b ≠ 0)
            (hpm : p.Monic) (hpi : Irreducible p) (hpdeg : p.natDegree = d)
            (hbdeg : b.natDegree < d) :
            symbol (Function.update (Function.update (polynomialTuple a ha) i
              (polynomialUnit F p hp)) j (polynomialUnit F b hb)) ∈
              generatedStage F n d := by
          let a' := Function.update (Function.update a i p) j b
          have ha' : ∀ l, a' l ≠ 0 :=
            update_nonzero _ (update_nonzero a ha i p hp) j b hb
          have hmem := ih (t.erase j) (Finset.erase_ssubset hjt) a' ha'
          have htop' : ∀ l ∈ t.erase j,
              (a' l).Monic ∧ Irreducible (a' l) ∧ (a' l).natDegree = d := by
            intro l hl
            obtain ⟨hlj, hlt⟩ := Finset.mem_erase.mp hl
            by_cases hli : l = i
            · subst l
              simpa [a', hij] using And.intro hpm (And.intro hpi hpdeg)
            · simpa [a', hlj, hli] using htop l hlt
          have hsmall' : ∀ l ∉ t.erase j, (a' l).natDegree < d := by
            intro l hl
            by_cases hlj : l = j
            · subst l
              simpa [a'] using hbdeg
            · have hlt : l ∉ t := fun h => hl (Finset.mem_erase.mpr ⟨hlj, h⟩)
              have hli : l ≠ i := fun h => hlt (h ▸ hit)
              simpa [a', hlj, hli] using hsmall l hlt
          have hfinal := hmem htop' hsmall'
          have heq : polynomialTuple a' ha' = Function.update
              (Function.update (polynomialTuple a ha) i (polynomialUnit F p hp))
              j (polynomialUnit F b hb) := by
            funext l
            by_cases hlj : l = j
            · subst l
              simp [polynomialTuple, a']
            · by_cases hli : l = i
              · subst l
                simp [polynomialTuple, a', hij]
              · simp [polynomialTuple, a', hlj, hli]
          rwa [heq] at hfinal
        have hpair := reduce_top_pair d hd (generatedStage F n d) (polynomialTuple a ha)
          i j hij (a i) (a j) hmi hmj hdi hdj
          (fun b hb hbdeg => hreduce (a i) b (ha i) hb hmi hii hdi hbdeg)
          (fun b hb hbdeg => hreduce (a j) b (ha j) hb hmj hijj hdj hbdeg)
        change symbol (Function.update (Function.update (polynomialTuple a ha) i
          (polynomialTuple a ha i)) j (polynomialTuple a ha j)) ∈ generatedStage F n d at hpair
        simpa only [Function.update_eq_self] using hpair
      · apply polynomial_symbol_mem_generatedStage_one_top d a ha i hmi hii hdi
        intro j hji
        apply hsmall j
        intro hj
        exact ht' ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩⟩
    · exact (show lower F (n + 1) d ≤ generatedStage F n d from le_sup_left)
        (polynomial_symbol_mem_lower d a ha (fun i => hsmall i (fun hi => ht ⟨i, hi⟩)))

/-- A tuple of small polynomials and monic top irreducibles is in the generated stage. -/
theorem atomic_tuple_mem (d : ℕ) (hd : 0 < d)
    (a : Fin (n + 1) → F[X]) (ha : ∀ i, a i ≠ 0)
    (hatom : ∀ i, degreeAtom d (a i)) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d := by
  classical
  apply atomic_tuple_mem_topSet d hd (Finset.univ.filter fun i => (a i).natDegree = d) a ha
  · intro i hi
    have heq := (Finset.mem_filter.mp hi).2
    rcases hatom i with hsmall | htop
    · omega
    · exact htop
  · intro i hi
    have hne : (a i).natDegree ≠ d := by simpa using hi
    exact (hatom i).resolve_right (fun h => hne h.2.2)

/-- Every individually bounded polynomial tuple lies in the next generated stage. -/
theorem polynomial_symbol_mem_generatedStage (d : ℕ) (hd : 0 < d)
    (a : Fin (n + 1) → F[X]) (ha : ∀ i, a i ≠ 0)
    (hdeg : ∀ i, (a i).natDegree ≤ d) :
    symbol (polynomialTuple a ha) ∈ generatedStage F n d := by
  let s : Set (RatFunc F)ˣ := {u | ∃ (p : F[X]) (hp : p ≠ 0),
    degreeAtom d p ∧ u = polynomialUnit F p hp}
  apply symbol_mem_of_coordinate_span (generatedStage F n d) s
  · intro b hb
    choose p hp hpd hpu using hb
    have heq : b = polynomialTuple p hp := funext hpu
    rw [heq]
    exact atomic_tuple_mem d hd p hp hpd
  · intro i
    apply normalized_factor_induction d hd
      (fun u => Additive.ofMul u ∈ Submodule.span ℤ (Additive.ofMul '' s))
      (Submodule.zero_mem _) ?_ ?_ ?_ (a i) (ha i) (hdeg i)
    · intro u v hu hv
      exact Submodule.add_mem _ hu hv
    · intro b hb hbdeg
      exact Submodule.subset_span ⟨_, ⟨b, hb, Or.inl hbdeg, rfl⟩, rfl⟩
    · intro p hp hpi hpdeg
      exact Submodule.subset_span ⟨_, ⟨p, hp.ne_zero, Or.inr ⟨hp, hpi, hpdeg⟩, rfl⟩, rfl⟩

/-- One true degree stage is generated by the preceding stage and final-slot top symbols. -/
theorem lower_succ_eq (d : ℕ) (hd : 0 < d) :
    lower F (n + 1) (d + 1) =
      lower F (n + 1) d ⊔ Submodule.span ℤ (topGenerators F n d) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, hdeg, rfl⟩
    exact polynomial_symbol_mem_generatedStage d hd a ha
      (fun i => Nat.lt_succ_iff.mp (hdeg i))
  · apply sup_le (lower_mono (Nat.le_succ d))
    apply Submodule.span_le.mpr
    rintro x ⟨p, a, hp, ha, _, _, hpdeg, hadeg, rfl⟩
    let b : Fin (n + 1) → F[X] := Fin.snoc a p
    have hb : ∀ i, b i ≠ 0 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [b] using hp
      · simpa [b] using ha j
    have hdeg : ∀ i, (b i).natDegree < d + 1 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [b, hpdeg]
      · simpa [b] using (hadeg j).trans (Nat.lt_succ_self d)
    have h := polynomial_symbol_mem_lower (d + 1) b hb hdeg
    have heq : Fin.snoc (polynomialTuple a ha) (polynomialUnit F p hp) =
        polynomialTuple b hb := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [b, polynomialTuple]
    rw [heq]
    exact h

end MilnorK.DegreeFiltration
