/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionFraction
public import Aglib.RingTheory.AdicCompletion.GeometricallyReducedFraction

/-! # The original parameter fraction field and its actual completion square -/

@[expose] public noncomputable section

open IsLocalRing

namespace AdicCompletion

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The explicit completion fraction map agrees with the canonical action used by the
intrinsic geometric-reducedness condition. -/
theorem fractionRingMap_eq_liftAlgebra :
    letI := faithfulSMul_maximalIdeal R
    letI := FractionRing.liftAlgebra R
      (FractionRing (AdicCompletion (maximalIdeal R) R))
    fractionRingMap R (FractionRing R) =
      algebraMap (FractionRing R) (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
  let := faithfulSMul_maximalIdeal R
  let := FractionRing.liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  let := FractionRing.isScalarTower_liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  apply IsFractionRing.ringHom_ext (A := R)
  intro r
  rw [fractionRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R)
      (FractionRing (AdicCompletion (maximalIdeal R) R)),
    ← IsScalarTower.algebraMap_apply R (FractionRing R)
      (FractionRing (AdicCompletion (maximalIdeal R) R))]

end AdicCompletion

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

attribute [local instance] isDiscreteValuationRing algebraMap_isLocalHom
  completionAlgebra completionAlgebra_isLocalHom

local notation "T" => Ring R ι p
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T
local notation "K₀" => FractionRing R
local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "Q₀" => MvPolynomial ι K₀
local notation "Q" => MvPolynomial ι K

/-- Extension of the actual R-to-completion fraction map to rational functions. -/
def rationalCoefficientCompletionMap : FractionRing Q₀ →+* FractionRing Q :=
  IsFractionRing.lift
    (g := (algebraMap Q (FractionRing Q)).comp
      (MvPolynomial.map (AdicCompletion.fractionRingMap R K₀)))
    ((IsFractionRing.injective Q (FractionRing Q)).comp
      (MvPolynomial.map_injective _ (AdicCompletion.fractionRingMap R K₀).injective))

omit [Finite ι] in
@[simp] theorem rationalCoefficientCompletionMap_algebraMap (q : Q₀) :
    rationalCoefficientCompletionMap R ι (algebraMap Q₀ (FractionRing Q₀) q) =
      algebraMap Q (FractionRing Q) (MvPolynomial.map (AdicCompletion.fractionRingMap R K₀) q) :=
  IsFractionRing.lift_algebraMap _ q

omit [Finite ι] in
/-- Original polynomials retain their actual completed coefficients through the rational lift. -/
theorem rationalCoefficientCompletionMap_original (q : MvPolynomial ι R) :
    rationalCoefficientCompletionMap R ι
        (algebraMap Q₀ (FractionRing Q₀) (MvPolynomial.map (algebraMap R K₀) q)) =
      algebraMap Q (FractionRing Q)
        (MvPolynomial.map (algebraMap A K) (MvPolynomial.map (algebraMap R A) q)) := by
  rw [rationalCoefficientCompletionMap_algebraMap]
  have hc : (AdicCompletion.fractionRingMap R K₀).comp (algebraMap R K₀) =
      (algebraMap A K).comp (algebraMap R A) := by
    ext r
    exact AdicCompletion.fractionRingMap_algebraMap R K₀ r
  rw [MvPolynomial.map_map, MvPolynomial.map_map, hc]

/-- The full fraction-field square commutes for the original parameter localization,
its actual completion, and both original and completed rational-function fields. -/
theorem completedRationalMap_parameterFractionEquiv :
    ((completedRationalMap R ι p).comp (rationalCoefficientCompletionMap R ι)).comp
        (parameterFractionEquiv R ι p).toRingHom =
      AdicCompletion.fractionRingMap T (FractionRing T) := by
  have hT : (((completedRationalMap R ι p).comp
        (rationalCoefficientCompletionMap R ι)).comp
        (parameterFractionEquiv R ι p).toRingHom).comp (algebraMap T (FractionRing T)) =
      (AdicCompletion.fractionRingMap T (FractionRing T)).comp
        (algebraMap T (FractionRing T)) := by
    apply IsLocalization.ringHom_ext (parameterIdeal R ι p).primeCompl
    apply RingHom.ext
    intro q
    change completedRationalMap R ι p (rationalCoefficientCompletionMap R ι
      (parameterFractionEquiv R ι p
        (algebraMap T (FractionRing T) (algebraMap (MvPolynomial ι R) T q)))) =
      AdicCompletion.fractionRingMap T (FractionRing T)
        (algebraMap T (FractionRing T) (algebraMap (MvPolynomial ι R) T q))
    rw [parameterFractionEquiv_polynomial, rationalCoefficientCompletionMap_original,
      completedRationalMap_map_algebraMap, completedPolynomialMap_map,
      AdicCompletion.fractionRingMap_algebraMap]
  exact IsFractionRing.ringHom_ext (fun t => RingHom.congr_fun hT t)

end ParameterLocalization
