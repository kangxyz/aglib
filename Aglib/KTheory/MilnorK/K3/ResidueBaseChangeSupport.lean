/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialResidueRestriction
public import Aglib.KTheory.MilnorK.K3.ResidueSupport
public import Aglib.RingTheory.PolynomialPlaceContraction

/-!
# Actual finite-residue support after coefficient extension

For an arbitrary extension of a characteristic-zero coefficient field, a
class supported at one finite source place restricts to a class supported at
the finitely many irreducible factors of that polynomial's coefficient image.
Each nonzero candidate coordinate is the original Milnor K₂ map on the actual
polynomial quotient fields. Target places with zero contraction are handled
by vanishing of all mapped polynomial-unit symbols, then symbol generation.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- Coefficient extension sends a literal polynomial unit to the literal
unit of its coefficient image. -/
theorem unitsMap_polynomialUnit (φ : k →+* L) (a : k[X]) (ha : a ≠ 0) :
    Units.map (fractionMap φ).toMonoidHom (polynomialUnit a ha) =
      polynomialUnit (a.map φ) (Polynomial.map_ne_zero ha) := by
  apply Units.ext
  exact fractionMap_polynomial φ a

/-- A target place dividing no nonzero source polynomial kills the restriction
of every actual Milnor K₃ class. No finite-place contraction is assumed. -/
theorem residueAt_restrict_zero_of_no_polynomial_divisor (φ : k →+* L) (q : L[X])
    [Fact (Irreducible q)] (hq : ∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ)
    (x : Group (RatFunc k)) :
    residueAt q (MilnorK.K3.map (fractionMap φ) x) = 0 := by
  have h : (residueAt q).comp (MilnorK.K3.map (fractionMap φ)) = 0 := by
    apply MilnorK.K3.linearMap_ext
    intro a b c
    have hna := hq (a : RatFunc k).num (RatFunc.num_ne_zero a.ne_zero)
    have hda := hq (a : RatFunc k).denom (RatFunc.denom_ne_zero _)
    have hnb := hq (b : RatFunc k).num (RatFunc.num_ne_zero b.ne_zero)
    have hdb := hq (b : RatFunc k).denom (RatFunc.denom_ne_zero _)
    have hnc := hq (c : RatFunc k).num (RatFunc.num_ne_zero c.ne_zero)
    have hdc := hq (c : RatFunc k).denom (RatFunc.denom_ne_zero _)
    change residueAt q (MilnorK.K3.map (fractionMap φ) (symbol3 a b c)) = 0
    rw [← polynomialUnit_num_div_denom a, ← polynomialUnit_num_div_denom b,
      ← polynomialUnit_num_div_denom c]
    simp only [symbol3_div_left, symbol3_div_middle, symbol3_div_right,
      map_sub, MilnorK.K3.map_symbol3, unitsMap_polynomialUnit]
    simp [residueAt_polynomial_units_zero, hna, hda, hnb, hdb, hnc, hdc]
  exact LinearMap.congr_fun h x

/-- The genuine finite set of target factors of a source place. -/
def placesAbove (φ : k →+* L) (p : MonicIrreducible k) : Finset (MonicIrreducible L) :=
  (finite_monicIrreducible_divisors (p.val.map φ)
    (Polynomial.map_ne_zero p.property.2.ne_zero)).toFinset

/-- Membership in the finite factor set means literal polynomial divisibility. -/
@[simp]
theorem mem_placesAbove (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) : q ∈ placesAbove φ p ↔ q.val ∣ p.val.map φ :=
  Set.Finite.mem_toFinset _

/-- A target factor receives the original quotient-field Milnor K₂ map of the
single source residue. -/
theorem totalResidue_restrict_single_of_dvd [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (z : MilnorK.K2.Group (AdjoinRoot p.val))
    (x : Group (RatFunc k)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : q.val ∣ p.val.map φ) :
    totalResidue (MilnorK.K3.map (fractionMap φ) x) q =
      MilnorK.K2.map (adjoinRootMap φ p.val q.val hq) z := by
  rw [totalResidue_apply, residueAt_restrict φ p.val q.val hq]
  have hp : residueAt p.val x = z := by
    simpa only [totalResidue_apply, DFinsupp.single_eq_same] using DFunLike.congr_fun hx p
  rw [hp]

/-- Every target place outside the factors of the source polynomial has zero
residue, including places whose contraction is zero. -/
theorem totalResidue_restrict_single_of_not_dvd [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (z : MilnorK.K2.Group (AdjoinRoot p.val))
    (x : Group (RatFunc k)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : ¬q.val ∣ p.val.map φ) :
    totalResidue (MilnorK.K3.map (fractionMap φ) x) q = 0 := by
  rcases finite_place_or_no_polynomial_divisor φ q.val q.property.2 with
      ⟨r, hrm, hri, hqr⟩ | hzero
  · let : Fact (Irreducible r) := ⟨hri⟩
    let r' : MonicIrreducible k := ⟨r, hrm, hri⟩
    have hrp : r' ≠ p := by
      intro h
      exact hq (by simpa only [← h] using hqr)
    have hr : residueAt r'.val x = 0 := by
      simpa only [totalResidue_apply, DFinsupp.single_eq_of_ne hrp] using
        DFunLike.congr_fun hx r'
    rw [totalResidue_apply, residueAt_restrict φ r'.val q.val hqr, hr, map_zero]
  · exact residueAt_restrict_zero_of_no_polynomial_divisor φ q.val hzero x

open scoped Classical in
/-- The actual dependent support is contained in the finite polynomial factor set. -/
theorem totalResidue_restrict_single_support_subset [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (z : MilnorK.K2.Group (AdjoinRoot p.val))
    (x : Group (RatFunc k)) [DecidableEq (MonicIrreducible k)]
    (hx : totalResidue x = DFinsupp.single p z) :
    (totalResidue (MilnorK.K3.map (fractionMap φ) x)).support ⊆ placesAbove φ p := by
  classical
  intro q hq
  apply (mem_placesAbove φ p q).mpr
  by_contra hnot
  exact (DFinsupp.mem_support_iff.mp hq)
    (totalResidue_restrict_single_of_not_dvd φ p z x hx q hnot)

end MilnorK.K3.PolynomialResidue
