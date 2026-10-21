/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalFormalField
public import Aglib.RingTheory.MvPolynomial.EvaluationComponent
public import Aglib.RingTheory.MvPowerSeries.FractionFieldSeparable

/-!
# Generic smoothness of the actual formal component over a field

The ambient fraction field is that of ordinary series over the original field.
The completed-coefficient formal target acts through its canonical coefficient
transport. Both actions of the polynomial ring agree literally, and the
rational-function action is the original native fraction lift. No separability
or generic-smoothness hypothesis is imposed on the formal point.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalRing

variable (k : Type*) [Field k] (n : ℕ)

local instance : IsDomain (FormalSeries k n) := by
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  exact MulEquiv.isDomain (MvPowerSeries (Fin n) k) (formalSeriesFieldEquiv k n).toMulEquiv

local instance {σ : Type*} (y : σ → FormalSeries k n) :
    (RingHom.ker (MvPolynomial.aeval (R := MvPolynomial (Fin n) k) y)).IsPrime :=
  RingHom.ker_isPrime _

/-- For every formal point over a field, the fraction field of its actual
polynomial evaluation component is formally smooth over the original
polynomial coefficient ring. -/
theorem formallySmooth_evaluation_residueField {σ : Type*} [Finite σ]
    (y : σ → FormalSeries k n) :
    Algebra.FormallySmooth (MvPolynomial (Fin n) k)
      (RingHom.ker (MvPolynomial.aeval (R := MvPolynomial (Fin n) k) y)).ResidueField := by
  let P := MvPolynomial (Fin n) k
  let S := MvPowerSeries (Fin n) k
  let C := FormalSeries k n
  let K := FractionRing P
  let L := FractionRing S
  let e := formalSeriesFieldEquiv k n
  let : Algebra C L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  let : IsFractionRing C L := isFractionRing_of_formalSeriesFieldEquiv k n L
  let : IsScalarTower P C L := IsScalarTower.of_algebraMap_eq fun p => by
    change algebraMap P L p = algebraMap S L (e (algebraMap P C p))
    rw [formalSeriesFieldEquiv_algebraMap]
    exact IsScalarTower.algebraMap_apply P S L p
  let := MvPowerSeries.faithfulSMul_mvPolynomial k (Fin n)
  let : Algebra K L := MvPowerSeries.fractionFieldAlgebra k (Fin n)
  let : IsScalarTower P K L := FractionRing.isScalarTower_liftAlgebra P L
  let : Algebra.IsTranscendentalSeparable K L :=
    MvPowerSeries.isTranscendentalSeparable_fractionRing_of_tower k (Fin n)
  have hPC : Function.Injective (algebraMap P C) := by
    intro p q hpq
    apply FaithfulSMul.algebraMap_injective P S
    have h := congrArg e hpq
    change formalSeriesFieldEquiv k n
      (algebraMap (MvPolynomial (Fin n) k) (FormalSeries k n) p) =
      formalSeriesFieldEquiv k n
        (algebraMap (MvPolynomial (Fin n) k) (FormalSeries k n) q) at h
    rw [formalSeriesFieldEquiv_algebraMap, formalSeriesFieldEquiv_algebraMap] at h
    exact h
  exact MvPolynomial.formallySmooth_evaluation_residueField_of_transcendentalSeparable
    (F := K) (L := L) y hPC

end PolynomialLocalRing
