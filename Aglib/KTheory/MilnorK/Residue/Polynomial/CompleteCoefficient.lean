/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.CompleteRoot
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalCompletion
public import Aglib.RingTheory.PowerSeriesConstantClosure

/-!
# The actual upper complete coefficient residue square

The DVR is the original integral closure of power series in the literal
constant root field over Laurent series. Its constants, residue equivalence,
and uniformizer are the proved constructions, not additional hypotheses.
The upper rational-function field map is exactly the one used for singleton
polynomial norm base change.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm.CompleteCoefficientResidue

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open PowerSeries.ConstantClosure
open scoped RatFunc

variable {k : Type*} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

local instance : Fact (Irreducible (p.val.map (algebraMap k (LaurentSeries k)))) :=
  ⟨(constantPolynomial p).property.2⟩

/-- The actual upper rational-function map into the literal complete root field. -/
def upperFieldMap : RatFunc (AdjoinRoot p.val) →+* TopField p :=
  rationalCoefficientLaurentMap p

omit [CharZero k] in
/-- The complete constant polynomial is exactly the coefficient image of the
original rational presentation. -/
theorem constantPolynomial_eq_rationalCoefficient_map :
    (constantPolynomial p).val = (rationalCoefficientPolynomial p).val.map
      (algebraMap (RatFunc k) (LaurentSeries k)) :=
  (rationalCoefficientPolynomial_map_laurent p).symm

omit [CharZero k] in
/-- The upper map is definitionally the map in polynomial norm base change,
so no new compatibility hypothesis or norm map is introduced. -/
theorem upperFieldMap_eq_rationalCompletionRootMap :
    upperFieldMap p = rationalCompletionRootMap p (constantPolynomial p)
      (constantPolynomial_eq_rationalCoefficient_map p) := rfl

@[simp]
theorem upperFieldMap_C (b : AdjoinRoot p.val) :
    upperFieldMap p (RatFunc.C b) = algebraMap (Closure p) (TopField p) (constantMap p b) :=
  (rationalCoefficientLaurentMap_C p b).trans (constantMap_apply p b).symm

omit [CharZero k] in
/-- The rational variable is the actual integral-closure uniformizer. -/
@[simp]
theorem upperFieldMap_X :
    upperFieldMap p RatFunc.X = algebraMap (Closure p) (TopField p)
      (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) := by
  change rationalCoefficientLaurentMap p RatFunc.X = _
  rw [rationalCoefficientLaurentMap_X,
    ← IsScalarTower.algebraMap_apply (PowerSeries k) (Closure p) (TopField p),
    IsScalarTower.algebraMap_apply (PowerSeries k) (LaurentSeries k) (TopField p)]
  congr 1
  change algebraMap (RatFunc k) (LaurentSeries k) RatFunc.X =
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k)
  simpa only [Polynomial.coe_X, RatFunc.coePolynomial_eq_algebraMap, RatFunc.algebraMap_X] using
    (RatFunc.coe_coe (X : k[X])).symm

/-- The upper local map is the actual localization lift of constants and the
power-series uniformizer into the integral closure. -/
def upperLocalMap : Ring (X : (AdjoinRoot p.val)[X]) →+* Closure p :=
  coefficientDVRLocalMap (constantMap p)
    (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) (residueEquiv p)
    (fun b => (residueEquiv_apply p b).symm) (uniformizer_irreducible p)

instance upperLocalMap_isLocalHom : IsLocalHom (upperLocalMap p) :=
  coefficientDVRLocalMap_isLocalHom _ _ _ _ _

/-- The actual upper ring and field maps commute. -/
theorem upperLocalMap_fraction (r : Ring (X : (AdjoinRoot p.val)[X])) :
    upperFieldMap p (algebraMap (Ring (X : (AdjoinRoot p.val)[X]))
      (RatFunc (AdjoinRoot p.val)) r) =
        algebraMap (Closure p) (TopField p) (upperLocalMap p r) :=
  coefficientDVRLocalMap_fraction (constantMap p)
    (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) (residueEquiv p)
    (fun b => (residueEquiv_apply p b).symm) (uniformizer_irreducible p)
    (upperFieldMap p) (upperFieldMap_C p) (upperFieldMap_X p) r

/-- The actual all-class upper residue square for the complete coefficient
integral closure. No local map, residue map or compatibility square is assumed. -/
theorem upper_residue_square (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (residueEquiv p).symm.toRingHom
      (DVR.residue (Closure p) (TopField p) n (map (n + 1) (upperFieldMap p) x)) =
        map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x) :=
  residueAt_X_eq_coefficientDVR_residue (constantMap p)
    (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) (residueEquiv p)
    (fun b => (residueEquiv_apply p b).symm) (uniformizer_irreducible p)
    (upperFieldMap p) (upperFieldMap_C p) (upperFieldMap_X p) n x

end MilnorK.PolynomialNorm.CompleteCoefficientResidue
