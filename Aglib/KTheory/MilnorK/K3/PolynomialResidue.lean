/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DVR
public import Aglib.RingTheory.PolynomialLocalResidue

/-!
# The actual finite-polynomial Milnor K₃ residue

At an irreducible polynomial `p` over an arbitrary field, compose the actual
uniformizer-independent DVR residue with the original Milnor K₂ map induced
by the literal residue-field equivalence to `AdjoinRoot p`. Polynomial entries
are genuine nonzero rational-function units, and their reduced entries are
the original quotient classes. Normalization and vanishing are proved through
the units of the actual localization at `(p)`.

No separability, finite-extension norm, reciprocity, or exactness is assumed
or asserted here.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialResidue

open Polynomial
open MilnorK.K2
open Polynomial.LocalResidue

variable {k : Type*} [Field k]

/-- A nonzero polynomial as its literal unit in the rational-function field. -/
def polynomialUnit (q : k[X]) (hq : q ≠ 0) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap k[X] (RatFunc k) q) (RatFunc.algebraMap_ne_zero hq)

@[simp]
theorem polynomialUnit_coe (q : k[X]) (hq : q ≠ 0) :
    (polynomialUnit q hq : RatFunc k) = algebraMap k[X] (RatFunc k) q := rfl

variable (p : k[X]) [Fact (Irreducible p)]

/-- The actual DVR residue, transported by the original Milnor K₂ field map. -/
def residueAt : Group (RatFunc k) →ₗ[ℤ] MilnorK.K2.Group (AdjoinRoot p) :=
  (MilnorK.K2.map (residueEquiv p).toRingHom).comp (DVR.residue (Ring p) (RatFunc k))

/-- A polynomial prime to `p` as a unit of the actual localization at `(p)`. -/
def localUnit (q : k[X]) (hq : ¬ p ∣ q) : (Ring p)ˣ :=
  ((isUnit_polynomial_iff p q).mpr hq).unit

@[simp]
theorem localUnit_coe (q : k[X]) (hq : ¬ p ∣ q) :
    (localUnit p q hq : Ring p) = algebraMap k[X] (Ring p) q :=
  ((isUnit_polynomial_iff p q).mpr hq).unit_spec

/-- The literal nonzero quotient class of a polynomial prime to `p`. -/
def quotientUnit (q : k[X]) (hq : ¬ p ∣ q) : (AdjoinRoot p)ˣ :=
  Units.mk0 (AdjoinRoot.mk p q) (AdjoinRoot.mk_eq_zero.not.mpr hq)

@[simp]
theorem quotientUnit_coe (q : k[X]) (hq : ¬ p ∣ q) :
    (quotientUnit p q hq : AdjoinRoot p) = AdjoinRoot.mk p q := rfl

/-- The local polynomial unit embeds as the original rational-function unit. -/
theorem fieldUnits_localUnit (q : k[X]) (hq : q ≠ 0) (hqp : ¬ p ∣ q) :
    MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) (localUnit p q hqp) =
      polynomialUnit q hq := by
  apply Units.ext
  change algebraMap (Ring p) (RatFunc k) (localUnit p q hqp : Ring p) =
    algebraMap k[X] (RatFunc k) q
  rw [localUnit_coe]
  exact (IsScalarTower.algebraMap_apply k[X] (Ring p) (RatFunc k) q).symm

/-- The uniformizer of the polynomial local ring is literally the rational function `p`. -/
theorem uniformizer_eq_polynomialUnit :
    MilnorK.K2.DVR.uniformizer (K := RatFunc k) (irreducible_polynomial p) =
      polynomialUnit p (Fact.out : Irreducible p).ne_zero := by
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply k[X] (Ring p) (RatFunc k) p).symm

/-- Actual reduction of a local polynomial unit is its literal quotient unit. -/
theorem residue_localUnit (q : k[X]) (hq : ¬ p ∣ q) :
    Units.map (residueEquiv p).toRingHom.toMonoidHom
        (Units.map (IsLocalRing.residue (Ring p)).toMonoidHom (localUnit p q hq)) =
      quotientUnit p q hq := by
  apply Units.ext
  change residueEquiv p
    (IsLocalRing.residue (Ring p) (localUnit p q hq : Ring p)) = AdjoinRoot.mk p q
  rw [localUnit_coe, residueEquiv_residue_polynomial]

/-- First-slot normalization for any polynomial entries prime to `p`. -/
theorem residueAt_polynomial_units (q r : k[X]) (hq : q ≠ 0) (hr : r ≠ 0)
    (hqp : ¬ p ∣ q) (hrp : ¬ p ∣ r) :
    residueAt p (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
      (polynomialUnit q hq) (polynomialUnit r hr)) =
      symbol (quotientUnit p q hqp) (quotientUnit p r hrp) := by
  rw [residueAt, LinearMap.comp_apply, ← uniformizer_eq_polynomialUnit p,
    ← fieldUnits_localUnit p q hq hqp, ← fieldUnits_localUnit p r hr hrp,
    DVR.residue_uniformizer_ring_units, MilnorK.K2.map_symbol,
    residue_localUnit, residue_localUnit]

/-- Monic reduced representatives give the literal finite-polynomial normalization. -/
theorem residueAt_reduced (hp : p.Monic) (q r : k[X])
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hqdeg : q.natDegree < p.natDegree) (hrdeg : r.natDegree < p.natDegree) :
    residueAt p (symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
      (polynomialUnit q hq) (polynomialUnit r hr)) =
      symbol (quotientUnit p q (hp.not_dvd_of_natDegree_lt hq hqdeg))
        (quotientUnit p r (hp.not_dvd_of_natDegree_lt hr hrdeg)) :=
  residueAt_polynomial_units p q r hq hr
    (hp.not_dvd_of_natDegree_lt hq hqdeg) (hp.not_dvd_of_natDegree_lt hr hrdeg)

/-- Three polynomials prime to `p` have zero residue through actual localized units. -/
theorem residueAt_polynomial_units_zero (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hap : ¬ p ∣ a) (hbp : ¬ p ∣ b) (hcp : ¬ p ∣ c) :
    residueAt p (symbol3 (polynomialUnit a ha) (polynomialUnit b hb)
      (polynomialUnit c hc)) = 0 := by
  rw [residueAt, LinearMap.comp_apply, ← fieldUnits_localUnit p a ha hap,
    ← fieldUnits_localUnit p b hb hbp, ← fieldUnits_localUnit p c hc hcp,
    DVR.residue_ring_units, map_zero]

/-- In particular, three nonzero polynomial entries coprime to `p` have zero residue. -/
theorem residueAt_coprime (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hap : IsCoprime p a) (hbp : IsCoprime p b) (hcp : IsCoprime p c) :
    residueAt p (symbol3 (polynomialUnit a ha) (polynomialUnit b hb)
      (polynomialUnit c hc)) = 0 :=
  residueAt_polynomial_units_zero p a b c ha hb hc
    ((Fact.out : Irreducible p).coprime_iff_not_dvd.mp hap)
    ((Fact.out : Irreducible p).coprime_iff_not_dvd.mp hbp)
    ((Fact.out : Irreducible p).coprime_iff_not_dvd.mp hcp)

end MilnorK.K3.PolynomialResidue
