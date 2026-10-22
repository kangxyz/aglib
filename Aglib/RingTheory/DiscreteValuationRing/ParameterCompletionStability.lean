/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionFrobenius
public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionSquare
public import Aglib.RingTheory.MvPolynomial.CoefficientFractionFrobenius
public import Aglib.RingTheory.AdicCompletion.GenericFormalFiber
public import Aglib.FieldTheory.SeparablyGenerated.FrobeniusBaseEquiv

/-!
# Geometric reducedness of the actual parameter DVR completion
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (π : R) [Fact (Irreducible π)]

attribute [local instance] isDiscreteValuationRing algebraMap_isLocalHom
  completionAlgebra completionAlgebra_isLocalHom MvPolynomial.algebraMvPolynomial

local notation "T" => Ring R ι π
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T
local notation "K₀" => FractionRing R
local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "Q₀" => MvPolynomial ι K₀
local notation "Q" => MvPolynomial ι K
local notation "F" => FractionRing Q₀
local notation "G" => FractionRing Q
local notation "S" => FractionRing T

/-- Positive-characteristic stability for the actual parameter DVR. The proof
uses only finite Frobenius independence, not a global p-basis or a finite
imperfection degree, and ends with the original fraction-completion action. -/
theorem hasGeometricallyReducedFractionCompletion_of_primeChar
    (p : ℕ) (hp : p.Prime) [CharP R p]
    (hR : AdicCompletion.HasGeometricallyReducedFractionCompletion R) :
    AdicCompletion.HasGeometricallyReducedFractionCompletion T := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : ExpChar K₀ p := expChar_of_injective_ringHom (IsFractionRing.injective R K₀) p
  let : ExpChar K p := expChar_of_injective_ringHom
    (AdicCompletion.fractionRingMap R K₀).injective p
  let : ExpChar L p := expChar_of_injective_ringHom
    (completionFractionMap R ι π).injective p
  let : ExpChar F p := expChar_of_injective_ringHom (algebraMap K₀ F).injective p
  let : ExpChar G p := expChar_of_injective_ringHom (algebraMap K G).injective p
  let : ExpChar S p := expChar_of_injective_ringHom
    (f := (algebraMap T S).comp (algebraMap R T))
    ((IsFractionRing.injective T S).comp (algebraMap_injective R ι π)) p
  let := AdicCompletion.faithfulSMul_maximalIdeal R
  let : Algebra K₀ K := AdicCompletion.fractionCompletionAlgebra R K₀
  have hK : Algebra.IsGeometricallyReduced K₀ K := by
    exact (congrArg (fun a : Algebra K₀ K =>
      @Algebra.IsGeometricallyReduced K₀ K _ _ a)
      (AdicCompletion.fractionCompletionAlgebra_eq_liftAlgebra R)).mpr hR
  let := hK
  let : Algebra Q₀ G := ((algebraMap Q G).comp (algebraMap Q₀ Q)).toAlgebra
  let : SMul Q G := (inferInstance : Algebra Q G).toSMul
  let : SMul Q₀ G := (inferInstance : Algebra Q₀ G).toSMul
  let : SMul Q₀ F := (inferInstance : Algebra Q₀ F).toSMul
  let : IsScalarTower Q₀ Q G :=
    IsScalarTower.of_algebraMap_eq (R := Q₀) («S» := Q) («A» := G) (fun _ => rfl)
  let : Algebra F G := (rationalCoefficientCompletionMap R ι).toAlgebra
  let : SMul F G := (inferInstance : Algebra F G).toSMul
  let : IsScalarTower Q₀ F G := by
    apply IsScalarTower.of_algebraMap_eq
    intro q
    exact (rationalCoefficientCompletionMap_algebraMap R ι q).symm
  have hFG : Algebra.IsGeometricallyReduced F G :=
    MvPolynomial.isGeometricallyReduced_fractionRing_of_geometricallyReduced_coefficients
      (k := K₀) («K» := K) (σ := ι) p hp
  let : Algebra G L := completedRationalAlgebra R ι π
  let : Algebra Q L := completedFractionPolynomialAlgebra R ι π
  let : IsScalarTower Q G L := completedFractionPolynomialAlgebra_tower R ι π
  have hGL : Algebra.IsGeometricallyReduced G L :=
    MvPolynomial.isGeometricallyReduced_fractionRing_of_finiteMonomialFrobeniusIndependent
      (k := K) («F» := G) («L» := L) (σ := ι) p hp
      (completionFiniteMonomialFrobeniusIndependent R ι π p hp)
  let : Algebra F L :=
    ((completedRationalMap R ι π).comp (rationalCoefficientCompletionMap R ι)).toAlgebra
  let : IsScalarTower F G L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hFL : Algebra.IsGeometricallyReduced F L := by
    apply Algebra.isGeometricallyReduced_of_finiteFrobeniusIndependence p hp
    exact Algebra.PreservesFiniteFrobeniusIndependence.trans p
      ((Algebra.isGeometricallyReduced_iff_finiteFrobeniusIndependence p hp).mp hFG)
      ((Algebra.isGeometricallyReduced_iff_finiteFrobeniusIndependence p hp).mp hGL)
  let : Algebra S L := AdicCompletion.fractionCompletionAlgebra T S
  have hsquare (s : S) : algebraMap S L s =
      algebraMap F L (parameterFractionEquiv R ι π s) := by
    exact (RingHom.congr_fun (completedRationalMap_parameterFractionEquiv R ι π) s).symm
  have hSL : Algebra.IsGeometricallyReduced S L := by
    exact Algebra.isGeometricallyReduced_of_baseRingEquiv p hp
      (parameterFractionEquiv R ι π) hsquare hFL
  let := AdicCompletion.faithfulSMul_maximalIdeal T
  exact (congrArg (fun a : Algebra S L =>
    @Algebra.IsGeometricallyReduced S L _ _ a)
    (AdicCompletion.fractionCompletionAlgebra_eq_liftAlgebra T)).mp hSL

/-- The intrinsic generic-completion condition is stable under the actual
parameter DVR localization. This theorem preserves arbitrary finite variable
universes and the canonical completed-fraction algebra action. -/
theorem hasGeometricallyReducedFractionCompletion
    (hR : AdicCompletion.HasGeometricallyReducedFractionCompletion R) :
    AdicCompletion.HasGeometricallyReducedFractionCompletion T := by
  rcases CharP.exists' R with hzero | ⟨p, hp, hchar⟩
  · let := hzero
    let : CharZero T := charZero_of_injective_ringHom (algebraMap_injective R ι π)
    exact AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero T
  · let := hchar
    exact hasGeometricallyReducedFractionCompletion_of_primeChar R ι π p hp.out hR

end ParameterLocalization
