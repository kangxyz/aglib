/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.DVR
public import Aglib.RingTheory.PolynomialLocalResidue

/-!
# Actual polynomial residues in every Milnor degree

The residue uses the actual polynomial DVR and the literal residue-field
identification with `AdjoinRoot p`. Its normalization places the polynomial
uniformizer in the last slot in every degree, including degree one. Polynomial
unit specialization is literal coordinatewise reduction. No finite-extension
norm, reciprocity or rational-function exactness is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable {k : Type*} [Field k]

/-- A nonzero polynomial as its literal unit in the rational-function field. -/
def polynomialUnit (q : k[X]) (hq : q ≠ 0) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap k[X] (RatFunc k) q) (RatFunc.algebraMap_ne_zero hq)

@[simp]
theorem polynomialUnit_coe (q : k[X]) (hq : q ≠ 0) :
    (polynomialUnit q hq : RatFunc k) = algebraMap k[X] (RatFunc k) q := rfl

variable (p : k[X]) [Fact (Irreducible p)]

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

/-- The finite residue obtained from the actual local ring and uniformizer `p`. -/
def residueAt (n : ℕ) : K (RatFunc k) (n + 1) →ₗ[ℤ] K (AdjoinRoot p) n :=
  (MilnorK.map n (residueEquiv p).toRingHom).comp
    (MilnorK.residue (MilnorK.K2.DVR.data (K := RatFunc k) (irreducible_polynomial p))
      (MilnorK.K2.DVR.unitReductionCompatible (irreducible_polynomial p)) n)

/-- The explicit-polynomial construction equals the canonical, uniformizer-independent DVR map. -/
theorem residueAt_eq_dvr (n : ℕ) :
    residueAt p n = (MilnorK.map n (residueEquiv p).toRingHom).comp
      (DVR.residue (Ring p) (RatFunc k) n) := by
  rw [DVR.residue_eq (Ring p) (RatFunc k) (irreducible_polynomial p) n]
  rfl

/-- Specialization at `p` uses its actual normalized local unit parts. -/
def specializeAt (n : ℕ) : K (RatFunc k) n →ₗ[ℤ] K (AdjoinRoot p) n :=
  (MilnorK.map n (residueEquiv p).toRingHom).comp
    (DVR.specializeWithUniformizer (Ring p) (RatFunc k) (irreducible_polynomial p) n)

/-- All actual localized ring-unit symbols have zero finite residue. -/
theorem residueAt_ring_units (n : ℕ) (a : Fin (n + 1) → (Ring p)ˣ) :
    residueAt p n (symbol (MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ a)) = 0 := by
  rw [residueAt, LinearMap.comp_apply, MilnorK.residue_symbol_units, map_zero]
  intro i
  exact MilnorK.K2.DVR.value_fieldUnits (Ring p) (RatFunc k) (a i)

/-- Last-slot normalization on actual localized ring units. -/
theorem residueAt_ring_units_uniformizer (n : ℕ) (a : Fin n → (Ring p)ˣ) :
    residueAt p n (symbol (Fin.snoc
      (MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ a)
      (polynomialUnit p (Fact.out : Irreducible p).ne_zero))) =
      symbol (fun i => Units.map (residueEquiv p).toRingHom.toMonoidHom
        (Units.map (IsLocalRing.residue (Ring p)).toMonoidHom (a i))) := by
  have hval : ∀ i, (MilnorK.K2.DVR.data (K := RatFunc k) (irreducible_polynomial p)).value
      (Additive.ofMul ((MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ a) i)) = 0 :=
    fun i => MilnorK.K2.DVR.value_fieldUnits (Ring p) (RatFunc k) (a i)
  have hnorm := MilnorK.residue_symbol_uniformizer
    (MilnorK.K2.DVR.data (K := RatFunc k) (irreducible_polynomial p))
    (MilnorK.K2.DVR.unitReductionCompatible (irreducible_polynomial p)) n
    (MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ a) hval
  change MilnorK.residue _ _ n (symbol (Fin.snoc _
    (MilnorK.K2.DVR.uniformizer (K := RatFunc k) (irreducible_polynomial p)))) = _ at hnorm
  rw [residueAt, LinearMap.comp_apply, ← uniformizer_eq_polynomialUnit p, hnorm,
    MilnorK.map_symbol]
  congr 1
  funext i
  change Units.map (residueEquiv p).toRingHom.toMonoidHom
    (MilnorK.K2.DVR.unitResidue (irreducible_polynomial p)
      (MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) (a i))) = _
  rw [MilnorK.K2.DVR.unitResidue_fieldUnits]

/-- Every tuple of nonzero polynomials prime to `p` has zero finite residue. -/
theorem residueAt_polynomial_units_zero (n : ℕ) (q : Fin (n + 1) → k[X])
    (hq : ∀ i, q i ≠ 0) (hqp : ∀ i, ¬ p ∣ q i) :
    residueAt p n (symbol (fun i => polynomialUnit (q i) (hq i))) = 0 := by
  have h : (fun i => polynomialUnit (q i) (hq i)) =
      MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ (fun i => localUnit p (q i) (hqp i)) := by
    funext i
    exact (fieldUnits_localUnit p (q i) (hq i) (hqp i)).symm
  rw [h]
  exact residueAt_ring_units p n _

/-- Last-slot normalization for any finite tuple of polynomial units. -/
theorem residueAt_polynomial_units (n : ℕ) (q : Fin n → k[X])
    (hq : ∀ i, q i ≠ 0) (hqp : ∀ i, ¬ p ∣ q i) :
    residueAt p n (symbol (Fin.snoc (fun i => polynomialUnit (q i) (hq i))
      (polynomialUnit p (Fact.out : Irreducible p).ne_zero))) =
      symbol (fun i => quotientUnit p (q i) (hqp i)) := by
  have h : (fun i => polynomialUnit (q i) (hq i)) =
      MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ (fun i => localUnit p (q i) (hqp i)) := by
    funext i
    exact (fieldUnits_localUnit p (q i) (hq i) (hqp i)).symm
  rw [h, residueAt_ring_units_uniformizer]
  congr 1
  funext i
  exact residue_localUnit p (q i) (hqp i)

/-- The finite specialization of polynomial units is their literal quotient tuple. -/
theorem specializeAt_polynomial_units (n : ℕ) (q : Fin n → k[X])
    (hq : ∀ i, q i ≠ 0) (hqp : ∀ i, ¬ p ∣ q i) :
    specializeAt p n (symbol (fun i => polynomialUnit (q i) (hq i))) =
      symbol (fun i => quotientUnit p (q i) (hqp i)) := by
  have h : (fun i => polynomialUnit (q i) (hq i)) =
      MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘ (fun i => localUnit p (q i) (hqp i)) := by
    funext i
    exact (fieldUnits_localUnit p (q i) (hq i) (hqp i)).symm
  rw [h, specializeAt, LinearMap.comp_apply, DVR.specializeWithUniformizer_ring_units,
    MilnorK.map_symbol]
  congr 1
  funext i
  exact residue_localUnit p (q i) (hqp i)

/-- Reduced representatives give the same literal last-slot normalization. -/
theorem residueAt_reduced (hp : p.Monic) (n : ℕ) (q : Fin n → k[X])
    (hq : ∀ i, q i ≠ 0) (hqdeg : ∀ i, (q i).natDegree < p.natDegree) :
    residueAt p n (symbol (Fin.snoc (fun i => polynomialUnit (q i) (hq i))
      (polynomialUnit p (Fact.out : Irreducible p).ne_zero))) =
      symbol (fun i => quotientUnit p (q i)
        (hp.not_dvd_of_natDegree_lt (hq i) (hqdeg i))) :=
  residueAt_polynomial_units p n q hq
    (fun i => hp.not_dvd_of_natDegree_lt (hq i) (hqdeg i))

end MilnorK.PolynomialResidue
