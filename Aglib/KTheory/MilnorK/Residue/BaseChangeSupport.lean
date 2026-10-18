/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.Restriction
public import Aglib.KTheory.MilnorK.Residue.Polynomial.Support
public import Aglib.RingTheory.PolynomialPlaceContraction

/-!
# Support of all-degree finite residues after coefficient extension

A rational class supported at one source place restricts to a class supported
at the finite set of factors of the coefficient image of that polynomial.
Every coordinate there is its actual quotient-field Milnor image. At target
places contracting to zero, mapped rational units are explicitly represented
by quotients of local polynomial units; residue vanishing follows without
expanding a symbol into numerator/denominator combinations.

The finite-factor support comparison assumes characteristic zero, as required
by the proved unramified finite residue square. Vanishing at zero-contraction
places works in every characteristic. No norm or tower law is asserted.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- Coefficient extension maps a literal polynomial unit to the unit of its
literal coefficient image. -/
theorem unitsMap_polynomialUnit (φ : k →+* L) (a : k[X]) (ha : a ≠ 0) :
    Units.map (fractionMap φ).toMonoidHom (polynomialUnit a ha) =
      polynomialUnit (a.map φ) (Polynomial.map_ne_zero ha) := by
  apply Units.ext
  exact fractionMap_polynomial φ a

/-- When no nonzero source polynomial maps to a multiple of a target place,
each mapped rational unit is an actual target local-ring unit. -/
theorem exists_localUnit_restrict_of_no_polynomial_divisor (φ : k →+* L) (q : L[X])
    [Fact (Irreducible q)] (hq : ∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ)
    (a : (RatFunc k)ˣ) :
    ∃ u : (Ring q)ˣ, MilnorK.K2.DVR.fieldUnits (Ring q) (RatFunc L) u =
      Units.map (fractionMap φ).toMonoidHom a := by
  refine ⟨localUnit q ((a : RatFunc k).num.map φ)
      (hq _ (RatFunc.num_ne_zero a.ne_zero)) /
    localUnit q ((a : RatFunc k).denom.map φ) (hq _ (RatFunc.denom_ne_zero _)), ?_⟩
  rw [_root_.map_div,
    fieldUnits_localUnit q _ (Polynomial.map_ne_zero (RatFunc.num_ne_zero a.ne_zero)),
    fieldUnits_localUnit q _ (Polynomial.map_ne_zero (RatFunc.denom_ne_zero _)),
    ← unitsMap_polynomialUnit φ _ (RatFunc.num_ne_zero a.ne_zero),
    ← unitsMap_polynomialUnit φ _ (RatFunc.denom_ne_zero _), ← _root_.map_div,
    polynomialUnit_num_div_denom]

/-- Zero-contraction target places kill restriction of every all-degree class,
because every restricted symbol consists of actual target local units. -/
theorem residueAt_restrict_zero_of_no_polynomial_divisor (φ : k →+* L) (q : L[X])
    [Fact (Irreducible q)] (hq : ∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ)
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    residueAt q n (MilnorK.map (n + 1) (fractionMap φ) x) = 0 := by
  have h : (residueAt q n).comp (MilnorK.map (n + 1) (fractionMap φ)) = 0 := by
    apply MilnorK.linearMap_ext
    intro a
    choose u hu using fun i =>
      exists_localUnit_restrict_of_no_polynomial_divisor φ q hq (a i)
    have ht : Units.map (fractionMap φ).toMonoidHom ∘ a =
        MilnorK.K2.DVR.fieldUnits (Ring q) (RatFunc L) ∘ u := by
      funext i
      exact (hu i).symm
    simp only [LinearMap.comp_apply, MilnorK.map_symbol, LinearMap.zero_apply, ht]
    exact residueAt_ring_units q n u
  exact LinearMap.congr_fun h x

/-- The actual finite set of monic irreducible target factors. -/
def placesAbove (φ : k →+* L) (p : MonicIrreducible k) : Finset (MonicIrreducible L) :=
  (finite_monicIrreducible_divisors (p.val.map φ)
    (Polynomial.map_ne_zero p.property.2.ne_zero)).toFinset

/-- The finite factor-set condition is literal polynomial divisibility. -/
@[simp] theorem mem_placesAbove (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) : q ∈ placesAbove φ p ↔ q.val ∣ p.val.map φ :=
  Set.Finite.mem_toFinset _

/-- At each factor, the single source residue becomes its actual quotient-field
Milnor image in every degree. -/
theorem totalResidue_restrict_single_of_dvd [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (z : K (AdjoinRoot p.val) n)
    (x : K (RatFunc k) (n + 1)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue n x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : q.val ∣ p.val.map φ) :
    totalResidue n (MilnorK.map (n + 1) (fractionMap φ) x) q =
      MilnorK.map n (adjoinRootMap φ p.val q.val hq) z := by
  rw [totalResidue_apply, residueAt_restrict φ p.val q.val hq]
  have hp : residueAt p.val n x = z := by
    simpa only [totalResidue_apply, DFinsupp.single_eq_same] using DFunLike.congr_fun hx p
  rw [hp]

/-- Every place outside the factors has zero restricted residue, including all
places whose contraction is zero. -/
theorem totalResidue_restrict_single_of_not_dvd [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (z : K (AdjoinRoot p.val) n)
    (x : K (RatFunc k) (n + 1)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue n x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : ¬q.val ∣ p.val.map φ) :
    totalResidue n (MilnorK.map (n + 1) (fractionMap φ) x) q = 0 := by
  rcases finite_place_or_no_polynomial_divisor φ q.val q.property.2 with
      ⟨r, hrm, hri, hqr⟩ | hzero
  · let : Fact (Irreducible r) := ⟨hri⟩
    let r' : MonicIrreducible k := ⟨r, hrm, hri⟩
    have hrp : r' ≠ p := by
      intro h
      exact hq (by simpa only [← h] using hqr)
    have hr : residueAt r'.val n x = 0 := by
      simpa only [totalResidue_apply, DFinsupp.single_eq_of_ne hrp] using
        DFunLike.congr_fun hx r'
    rw [totalResidue_apply, residueAt_restrict φ r'.val q.val hqr, hr, map_zero]
  · exact residueAt_restrict_zero_of_no_polynomial_divisor φ q.val hzero n x

open scoped Classical in
/-- The actual dependent residue support lies in the actual finite factor set. -/
theorem totalResidue_restrict_single_support_subset [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (z : K (AdjoinRoot p.val) n)
    (x : K (RatFunc k) (n + 1)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue n x = DFinsupp.single p z) :
    (totalResidue n (MilnorK.map (n + 1) (fractionMap φ) x)).support ⊆ placesAbove φ p := by
  classical
  intro q hq
  apply (mem_placesAbove φ p q).mpr
  by_contra hnot
  exact (DFinsupp.mem_support_iff.mp hq)
    (totalResidue_restrict_single_of_not_dvd φ n p z x hx q hnot)

end MilnorK.PolynomialResidue
