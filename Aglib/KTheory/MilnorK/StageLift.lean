/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.DegreeFiltration
public import Aglib.KTheory.MilnorK.Residue.Polynomial.Basic
public import Aglib.KTheory.MilnorK.TupleSymbols

/-!
# Canonical residue-field lifts in every Milnor degree

Canonical reduced representatives lift residue-field symbols to the actual
polynomial degree quotient, with the irreducible polynomial in the final slot.
Every degree estimate is coordinatewise. The empty tuple is included, so the
degree-zero source lifts to the degree-one symbol of the polynomial itself.
-/

@[expose] public noncomputable section

namespace MilnorK.DegreeFiltration

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- Inserting two smaller polynomial entries preserves the genuine lower stage. -/
theorem snoc_update_polynomial_mem_lower (d : ℕ) (a : Fin n → F[X])
    (ha : ∀ i, a i ≠ 0) (hdeg : ∀ i, (a i).natDegree < d)
    (i : Fin n) (b c : F[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbdeg : b.natDegree < d) (hcdeg : c.natDegree < d) :
    symbol (Fin.snoc (Function.update (polynomialTuple a ha) i (polynomialUnit F b hb))
      (polynomialUnit F c hc)) ∈ lower F (n + 1) d := by
  classical
  let q : Fin (n + 1) → F[X] := Fin.snoc (Function.update a i b) c
  have hq : ∀ j, q j ≠ 0 := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [q, Fin.snoc_last] using hc
    · by_cases h : k = i
      · subst k
        simpa [q] using hb
      · simpa [q, h] using ha k
  have hqdeg : ∀ j, (q j).natDegree < d := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [q, Fin.snoc_last] using hcdeg
    · by_cases h : k = i
      · subst k
        simpa [q] using hbdeg
      · simpa [q, h] using hdeg k
  have heq : Fin.snoc
      (Function.update (polynomialTuple a ha) i (polynomialUnit F b hb))
      (polynomialUnit F c hc) = polynomialTuple q hq := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [polynomialTuple, q, Fin.snoc_last]
    · by_cases h : k = i
      · subst k
        simp [polynomialTuple, q]
      · simp [polynomialTuple, q, h]
  rw [heq]
  exact polynomial_symbol_mem_lower d q hq hqdeg

private theorem symbol_pair_correction {L : Type*} [Field L]
    (p a b c f : Lˣ) (hsum : (f : L) * p + (a : L) * b = c) :
    MilnorK.K2.symbol a p + MilnorK.K2.symbol b p - MilnorK.K2.symbol c p =
      -MilnorK.K2.symbol (a * b / c) (f / c) := by
  have hnormalized : ((a * b / c : Lˣ) : L) + (((f / c) * p : Lˣ) : L) = 1 := by
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_eq_mul_div, ← add_div, add_comm, hsum, div_self c.ne_zero]
  have hs := MilnorK.K2.steinberg (a * b / c) ((f / c) * p) hnormalized
  rw [MilnorK.K2.symbol_mul_right, MilnorK.K2.symbol_div_left _ _ p,
    MilnorK.K2.symbol_mul_left] at hs
  exact eq_neg_of_add_eq_zero_right hs


variable (p : F[X]) [Fact (Irreducible p)]


/-- Reduced multiplication in any coordinate holds modulo the actual lower stage.
All other entries and both factors are bounded individually, with no bound on their sum. -/
theorem reduced_mul_coordinate_mem_lower (hp : p.Monic) (a : Fin n → F[X])
    (ha : ∀ i, a i ≠ 0) (hdeg : ∀ i, (a i).natDegree < p.natDegree)
    (i : Fin n) (b c : F[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbdeg : b.natDegree < p.natDegree) (hcdeg : c.natDegree < p.natDegree) :
    symbol (Fin.snoc (Function.update (polynomialTuple a ha) i (polynomialUnit F b hb))
        (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) +
      symbol (Fin.snoc (Function.update (polynomialTuple a ha) i (polynomialUnit F c hc))
        (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) -
      symbol (Fin.snoc (Function.update (polynomialTuple a ha) i
        (polynomialUnit F ((b * c) %ₘ p) (reduced_mul_ne_zero p hp b c hb hc hbdeg hcdeg)))
        (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) ∈
      lower F (n + 1) p.natDegree := by
  let q := (b * c) %ₘ p
  have hq := reduced_mul_ne_zero p hp b c hb hc hbdeg hcdeg
  have hqdeg := reduced_mul_natDegree_lt p hp b c
  have hij : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
  let T := pairMap (Fin.snoc (polynomialTuple a ha) 1) i.castSucc (Fin.last n) hij
  have hT (u v : (RatFunc F)ˣ) :
      T (MilnorK.K2.symbol u v) =
        symbol (Fin.snoc (Function.update (polynomialTuple a ha) i u) v) := by
    dsimp [T]
    rw [← Fin.snoc_update, Fin.update_snoc_last]
  have hsmall (u v : F[X]) (hu : u ≠ 0) (hv : v ≠ 0)
      (hudeg : u.natDegree < p.natDegree) (hvdeg : v.natDegree < p.natDegree) :
      T (MilnorK.K2.symbol (polynomialUnit F u hu) (polynomialUnit F v hv)) ∈
        lower F (n + 1) p.natDegree := by
    rw [hT]
    exact snoc_update_polynomial_mem_lower p.natDegree a ha hdeg i u v hu hv hudeg hvdeg
  by_cases heq : b * c = q
  · have heqUnit : polynomialUnit F q hq = polynomialUnit F b hb * polynomialUnit F c hc := by
      rw [← polynomialUnit_mul b c hb hc]
      congr 1
      exact heq.symm
    change _ + _ - symbol (Fin.snoc (Function.update (polynomialTuple a ha) i
      (polynomialUnit F q hq)) _) ∈ _
    rw [heqUnit]
    simp only [Fin.snoc_update, symbol_mul, sub_self]
    exact (lower F (n + 1) p.natDegree).zero_mem
  · obtain ⟨f, hf, hfdeg, hfeq⟩ := reduced_mul_correction p hp b c hb hc hbdeg hcdeg heq
    have hsum : (polynomialUnit F f hf : RatFunc F) *
          (polynomialUnit F p (Fact.out : Irreducible p).ne_zero : RatFunc F) +
        (polynomialUnit F b hb : RatFunc F) * (polynomialUnit F c hc : RatFunc F) =
          (polynomialUnit F q hq : RatFunc F) := by
      simpa only [polynomialUnit_coe, map_add, map_mul, add_comm] using
        congrArg (algebraMap F[X] (RatFunc F)) hfeq.symm
    have hid := congrArg T (symbol_pair_correction
      (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)
      (polynomialUnit F b hb) (polynomialUnit F c hc) (polynomialUnit F q hq)
      (polynomialUnit F f hf) hsum)
    simp only [map_sub, map_add, map_neg, hT] at hid
    change _ + _ - symbol (Fin.snoc (Function.update (polynomialTuple a ha) i
      (polynomialUnit F q hq)) _) ∈ _
    rw [hid, ← hT]
    apply (lower F (n + 1) p.natDegree).neg_mem
    rw [MilnorK.K2.symbol_div_left, MilnorK.K2.symbol_div_right, MilnorK.K2.symbol_div_right,
      MilnorK.K2.symbol_mul_left, MilnorK.K2.symbol_mul_left, map_sub, map_sub, map_sub,
      map_add, map_add]
    exact (lower F (n + 1) p.natDegree).sub_mem
      ((lower F (n + 1) p.natDegree).sub_mem
        ((lower F (n + 1) p.natDegree).add_mem
          (hsmall b f hb hf hbdeg hfdeg) (hsmall c f hc hf hcdeg hfdeg))
        ((lower F (n + 1) p.natDegree).add_mem
          (hsmall b q hb hq hbdeg hqdeg) (hsmall c q hc hq hcdeg hqdeg)))
      ((lower F (n + 1) p.natDegree).sub_mem
        (hsmall q f hq hf hqdeg hfdeg) (hsmall q q hq hq hqdeg hqdeg))


/-- The canonical reduced polynomial representing a residue-field unit. -/
def reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) : F[X] :=
  AdjoinRoot.modByMonicHom hp (a : AdjoinRoot p)

@[simp] theorem mk_reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    AdjoinRoot.mk p (reducedRepresentative p hp a) = (a : AdjoinRoot p) :=
  AdjoinRoot.mk_leftInverse hp (a : AdjoinRoot p)

/-- A unit has a nonzero canonical polynomial representative. -/
theorem reducedRepresentative_ne_zero (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp a ≠ 0 := by
  intro hzero
  have h := mk_reducedRepresentative p hp a
  rw [hzero, map_zero] at h
  exact a.ne_zero h.symm

/-- Each canonical representative has degree strictly smaller than the modulus. -/
theorem reducedRepresentative_natDegree_lt (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    (reducedRepresentative p hp a).natDegree < p.natDegree := by
  have h : reducedRepresentative p hp a %ₘ p = reducedRepresentative p hp a := by
    rw [← AdjoinRoot.modByMonicHom_mk hp, mk_reducedRepresentative]
    rfl
  rw [← h]
  exact natDegree_modByMonic_lt _ hp (Fact.out : Irreducible p).ne_one

/-- Multiplication of residue-field units reduces the polynomial product. -/
theorem reducedRepresentative_mul (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    reducedRepresentative p hp (a * b) =
      (reducedRepresentative p hp a * reducedRepresentative p hp b) %ₘ p := by
  rw [← AdjoinRoot.modByMonicHom_mk hp, map_mul, mk_reducedRepresentative,
    mk_reducedRepresentative]
  rfl

/-- The canonical representative considered as a rational-function unit. -/
def reducedUnit (hp : p.Monic) (a : (AdjoinRoot p)ˣ) : (RatFunc F)ˣ :=
  polynomialUnit F (reducedRepresentative p hp a) (reducedRepresentative_ne_zero p hp a)

/-- The unit lift of a product is the literal reduced polynomial product. -/
theorem reducedUnit_mul (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    reducedUnit p hp (a * b) =
      polynomialUnit F ((reducedRepresentative p hp a * reducedRepresentative p hp b) %ₘ p)
        (reduced_mul_ne_zero p hp _ _ (reducedRepresentative_ne_zero p hp a)
          (reducedRepresentative_ne_zero p hp b) (reducedRepresentative_natDegree_lt p hp a)
          (reducedRepresentative_natDegree_lt p hp b)) := by
  apply Units.ext
  simp only [reducedUnit, polynomialUnit_coe, reducedRepresentative_mul]

/-- The canonical reduced tuple of rational-function units. -/
def reducedTuple (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n) :
    SymbolTuple (RatFunc F) n := fun i => reducedUnit p hp (a i)

/-- Canonical reduction commutes with replacement in one coordinate. -/
theorem reducedTuple_update (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n)
    (i : Fin n) (b : (AdjoinRoot p)ˣ) :
    reducedTuple p hp (Function.update a i b) =
      Function.update (reducedTuple p hp a) i (reducedUnit p hp b) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [reducedTuple]
  · simp [reducedTuple, h]

/-- The canonical lifted symbol has the polynomial in its final slot. -/
def stageSymbol (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n) :
    K (RatFunc F) (n + 1) ⧸ lower F (n + 1) p.natDegree :=
  (lower F (n + 1) p.natDegree).mkQ
    (symbol (Fin.snoc (reducedTuple p hp a)
      (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)))

/-- Coordinatewise multiplication holds in the genuine lower-stage quotient. -/
theorem stageSymbol_mul (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n)
    (i : Fin n) (b c : (AdjoinRoot p)ˣ) :
    stageSymbol p hp (Function.update a i (b * c)) =
      stageSymbol p hp (Function.update a i b) + stageSymbol p hp (Function.update a i c) := by
  unfold stageSymbol
  simp only [reducedTuple_update]
  rw [reducedUnit_mul]
  symm
  rw [← map_add]
  exact (Submodule.Quotient.eq _).mpr
    (reduced_mul_coordinate_mem_lower p hp (fun j => reducedRepresentative p hp (a j))
      (fun j => reducedRepresentative_ne_zero p hp (a j))
      (fun j => reducedRepresentative_natDegree_lt p hp (a j)) i
      (reducedRepresentative p hp b) (reducedRepresentative p hp c)
      (reducedRepresentative_ne_zero p hp b) (reducedRepresentative_ne_zero p hp c)
      (reducedRepresentative_natDegree_lt p hp b) (reducedRepresentative_natDegree_lt p hp c))

/-- Reduced Steinberg relations hold literally before taking the stage quotient. -/
theorem reducedTuple_steinberg (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n)
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (hab : (a i : AdjoinRoot p) + (a j : AdjoinRoot p) = 1) :
    symbol (Fin.snoc (reducedTuple p hp a)
      (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) = 0 := by
  apply steinberg _ i.castSucc j.castSucc hij
  simp only [Fin.snoc_castSucc, reducedTuple, reducedUnit, polynomialUnit_coe]
  have h := reduced_add_eq_one p hp (reducedRepresentative p hp (a i))
    (reducedRepresentative p hp (a j)) (reducedRepresentative_natDegree_lt p hp (a i))
    (reducedRepresentative_natDegree_lt p hp (a j)) (by simpa using hab)
  simpa only [map_add, map_one] using congrArg (algebraMap F[X] (RatFunc F)) h

/-- The actual stage quotient kills every defining adjacent Steinberg relation. -/
theorem stageSymbol_steinberg (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n)
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (hab : (a i : AdjoinRoot p) + (a j : AdjoinRoot p) = 1) :
    stageSymbol p hp a = 0 := by
  unfold stageSymbol
  rw [reducedTuple_steinberg p hp a i j hij hab, map_zero]

/-- The canonical stage symbols satisfy exactly the original quotient relations. -/
theorem stageSymbol_isSymbolMap (hp : p.Monic) (n : ℕ) :
    IsSymbolMap (stageSymbol p hp (n := n)) :=
  ⟨stageSymbol_mul p hp, stageSymbol_steinberg p hp⟩

/-- The actual integer-linear stage lift from the original all-degree Milnor quotient. -/
def stageLift (hp : p.Monic) (n : ℕ) :
    K (AdjoinRoot p) n →ₗ[ℤ] K (RatFunc F) (n + 1) ⧸ lower F (n + 1) p.natDegree :=
  lift (stageSymbol p hp) (stageSymbol_isSymbolMap p hp n)

/-- The stage lift has its literal canonical reduced-symbol value. -/
@[simp] theorem stageLift_symbol (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n) :
    stageLift p hp n (symbol a) =
      (lower F (n + 1) p.natDegree).mkQ
        (symbol (Fin.snoc (reducedTuple p hp a)
          (polynomialUnit F p (Fact.out : Irreducible p).ne_zero))) :=
  lift_symbol _ _ a

/-- In degree zero the empty source symbol lifts to the one-entry symbol of `p`. -/
theorem stageLift_empty (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) 0) :
    stageLift p hp 0 (symbol a) = (lower F 1 p.natDegree).mkQ
      (symbol (fun _ : Fin 1 => polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) := by
  rw [stageLift_symbol, Fin.snoc_zero]

/-- The actual polynomial residue annihilates the entire lower-degree stage. -/
theorem lower_le_ker_residueAt (hp : p.Monic) (n : ℕ) :
    lower F (n + 1) p.natDegree ≤ LinearMap.ker (PolynomialResidue.residueAt p n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, hdeg, rfl⟩
  exact PolynomialResidue.residueAt_polynomial_units_zero p n a ha
    (fun i => hp.not_dvd_of_natDegree_lt (ha i) (hdeg i))

/-- The actual polynomial residue descends through the actual lower stage. -/
def stageResidue (hp : p.Monic) (n : ℕ) :
    (K (RatFunc F) (n + 1) ⧸ lower F (n + 1) p.natDegree) →ₗ[ℤ]
      K (AdjoinRoot p) n :=
  (lower F (n + 1) p.natDegree).liftQ (PolynomialResidue.residueAt p n)
    (lower_le_ker_residueAt p hp n)

theorem stageResidue_mkQ (hp : p.Monic) (n : ℕ) (x : K (RatFunc F) (n + 1)) :
    stageResidue p hp n ((lower F (n + 1) p.natDegree).mkQ x) =
      PolynomialResidue.residueAt p n x := rfl

/-- An already reduced polynomial is unchanged by canonical reduction. -/
theorem reducedRepresentative_quotientUnit (hp : p.Monic) (a : F[X])
    (ha : a ≠ 0) (hadeg : a.natDegree < p.natDegree) :
    reducedRepresentative p hp
      (PolynomialResidue.quotientUnit p a (hp.not_dvd_of_natDegree_lt ha hadeg)) = a := by
  change AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk p a) = a
  rw [AdjoinRoot.modByMonicHom_mk, modByMonic_eq_self_iff hp]
  exact degree_lt_degree hadeg

/-- Literal reduction of a canonical representative recovers its original unit. -/
@[simp] theorem quotientUnit_reducedRepresentative (hp : p.Monic) (a : (AdjoinRoot p)ˣ) :
    PolynomialResidue.quotientUnit p (reducedRepresentative p hp a)
      (hp.not_dvd_of_natDegree_lt (reducedRepresentative_ne_zero p hp a)
        (reducedRepresentative_natDegree_lt p hp a)) = a := by
  apply Units.ext
  exact mk_reducedRepresentative p hp a

/-- The actual descended residue recovers every original symbol, including the empty tuple. -/
@[simp] theorem stageResidue_stageSymbol (hp : p.Monic) (a : SymbolTuple (AdjoinRoot p) n) :
    stageResidue p hp n (stageSymbol p hp a) = symbol a := by
  unfold stageSymbol
  rw [stageResidue_mkQ]
  change PolynomialResidue.residueAt p n (symbol (Fin.snoc
    (fun i => PolynomialResidue.polynomialUnit (reducedRepresentative p hp (a i))
      (reducedRepresentative_ne_zero p hp (a i)))
    (PolynomialResidue.polynomialUnit p (Fact.out : Irreducible p).ne_zero))) = _
  rw [PolynomialResidue.residueAt_reduced p hp n _ _
    (fun i => reducedRepresentative_natDegree_lt p hp (a i))]
  simp only [quotientUnit_reducedRepresentative]

/-- On already reduced polynomial entries, the stage lift is the expected last-slot symbol. -/
theorem stageLift_reduced (hp : p.Monic) (a : Fin n → F[X]) (ha : ∀ i, a i ≠ 0)
    (hdeg : ∀ i, (a i).natDegree < p.natDegree) :
    stageLift p hp n (symbol (fun i => PolynomialResidue.quotientUnit p (a i)
      (hp.not_dvd_of_natDegree_lt (ha i) (hdeg i)))) =
      (lower F (n + 1) p.natDegree).mkQ
        (symbol (Fin.snoc (polynomialTuple a ha)
          (polynomialUnit F p (Fact.out : Irreducible p).ne_zero))) := by
  rw [stageLift_symbol]
  have heq : reducedTuple p hp (fun i => PolynomialResidue.quotientUnit p (a i)
      (hp.not_dvd_of_natDegree_lt (ha i) (hdeg i))) = polynomialTuple a ha := by
    funext i
    apply Units.ext
    change algebraMap F[X] (RatFunc F) (reducedRepresentative p hp
      (PolynomialResidue.quotientUnit p (a i) _)) = algebraMap F[X] (RatFunc F) (a i)
    rw [reducedRepresentative_quotientUnit p hp (a i) (ha i) (hdeg i)]
  rw [heq]

/-- The actual stage residue is a left inverse on every class of the original Milnor group. -/
theorem stageResidue_comp_stageLift (hp : p.Monic) (n : ℕ) :
    (stageResidue p hp n).comp (stageLift p hp n) = LinearMap.id := by
  apply linearMap_ext
  intro a
  change stageResidue p hp n (stageLift p hp n (symbol a)) = symbol a
  rw [stageLift, lift_symbol, stageResidue_stageSymbol]

@[simp] theorem stageResidue_stageLift (hp : p.Monic) (n : ℕ) (x : K (AdjoinRoot p) n) :
    stageResidue p hp n (stageLift p hp n x) = x :=
  LinearMap.congr_fun (stageResidue_comp_stageLift p hp n) x

/-- Canonical lifting into the actual lower-stage quotient is injective. -/
theorem stageLift_injective (hp : p.Monic) (n : ℕ) :
    Function.Injective (stageLift p hp n) :=
  Function.LeftInverse.injective (stageResidue_stageLift p hp n)

/-- The actual residue of the lower-stage quotient is surjective. -/
theorem stageResidue_surjective (hp : p.Monic) (n : ℕ) :
    Function.Surjective (stageResidue p hp n) :=
  Function.RightInverse.surjective (stageResidue_stageLift p hp n)

end MilnorK.DegreeFiltration
