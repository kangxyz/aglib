/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletion
public import Aglib.RingTheory.Localization.OriginalFraction

/-! # The actual rational function field over completed coefficients -/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace MvPolynomial

attribute [local instance] algebraMvPolynomial

/-- The coefficient-localization fraction equivalence retains every original polynomial. -/
theorem coefficientFractionEquiv_map_algebraMap
    (R : Type u) [CommRing R] [IsDomain R] (ι : Type v) (q : MvPolynomial ι R) :
    coefficientFractionEquiv R ι
        (algebraMap (MvPolynomial ι (FractionRing R))
          (FractionRing (MvPolynomial ι (FractionRing R)))
            (map (algebraMap R (FractionRing R)) q)) =
      algebraMap (MvPolynomial ι R) (FractionRing (MvPolynomial ι R)) q := by
  let M := (nonZeroDivisors R).map (C (σ := ι))
  let := IsLocalization.originalFractionAlgebra (MvPolynomial ι R)
    (MvPolynomial ι (FractionRing R)) M (coefficient_nonZeroDivisors_le R ι)
  change coefficientFractionEquiv R ι
    (algebraMap (MvPolynomial ι (FractionRing R)) _
      (algebraMap (MvPolynomial ι R) (MvPolynomial ι (FractionRing R)) q)) = _
  rw [(coefficientFractionEquiv R ι).commutes]
  exact IsLocalization.toOriginalFractionRing_algebraMap _ _ _ _ q

end MvPolynomial

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

attribute [local instance] MvPolynomial.algebraMvPolynomial
  isDiscreteValuationRing algebraMap_isLocalHom
  completionAlgebra completionAlgebra_isLocalHom

local notation "T" => Ring R ι p
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T
local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "Q" => MvPolynomial ι K

/-- Khat(Z) maps into Frac(That) through the genuine coefficient-localization equivalence. -/
def completedRationalMap : FractionRing Q →+* L :=
  (completedPolynomialFractionMap R ι p).comp
    (MvPolynomial.coefficientFractionEquiv A ι).toRingHom

/-- This is an embedding of fields, not an abstract identification of completion carriers. -/
theorem completedRationalMap_injective : Function.Injective (completedRationalMap R ι p) :=
  (completedRationalMap R ι p).injective

/-- The rational-function map agrees with the actual completed polynomial evaluation. -/
@[simp] theorem completedRationalMap_map_algebraMap (q : MvPolynomial ι A) :
    completedRationalMap R ι p
        (algebraMap Q (FractionRing Q) (MvPolynomial.map (algebraMap A K) q)) =
      algebraMap B L (completedPolynomialMap R ι p q) := by
  change completedPolynomialFractionMap R ι p
    (MvPolynomial.coefficientFractionEquiv A ι
      (algebraMap Q (FractionRing Q) (MvPolynomial.map (algebraMap A K) q))) = _
  rw [MvPolynomial.coefficientFractionEquiv_map_algebraMap,
    completedPolynomialFractionMap_algebraMap]

/-- The literal parameter variables are preserved. -/
@[simp] theorem completedRationalMap_X (i : ι) :
    completedRationalMap R ι p (algebraMap Q (FractionRing Q) (MvPolynomial.X i)) =
      algebraMap B L (completedVariable R ι p i) := by
  simpa only [MvPolynomial.map_X, completedPolynomialMap, MvPolynomial.aeval_X] using
    completedRationalMap_map_algebraMap R ι p (MvPolynomial.X i)

/-- On completed coefficients, the rational map is exactly the previously
constructed fraction map. -/
theorem completedRationalMap_coeff :
    (completedRationalMap R ι p).comp (algebraMap K (FractionRing Q)) =
      completionFractionMap R ι p := by
  apply IsFractionRing.ringHom_ext («A» := A)
  intro a
  change completedRationalMap R ι p
    (algebraMap K (FractionRing Q) (algebraMap A K a)) =
      completionFractionMap R ι p (algebraMap A K a)
  rw [completionFractionMap_algebraMap,
    IsScalarTower.algebraMap_apply K Q (FractionRing Q)]
  change completedRationalMap R ι p
    (algebraMap Q (FractionRing Q) (MvPolynomial.C (algebraMap A K a))) = _
  rw [← MvPolynomial.map_C, completedRationalMap_map_algebraMap]
  change algebraMap B L (MvPolynomial.aeval (completedVariable R ι p) (MvPolynomial.C a)) = _
  rw [MvPolynomial.aeval_C]
  rfl

/-- The canonical coefficient-fraction action; it is not silently replaced by a different lift. -/
abbrev completionFractionAlgebra : Algebra K L := (completionFractionMap R ι p).toAlgebra

/-- The rational-function action comes from the actual map just constructed. -/
abbrev completedRationalAlgebra : Algebra (FractionRing Q) L :=
  (completedRationalMap R ι p).toAlgebra

attribute [local instance] completionFractionAlgebra completedRationalAlgebra

/-- The field tower is certified by the literal coefficient square. -/
theorem completedRationalAlgebra_tower : IsScalarTower K (FractionRing Q) L := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (RingHom.congr_fun (completedRationalMap_coeff R ι p) a).symm

/-- The coefficient fraction action extends the original completed coefficient map. -/
theorem completionFractionAlgebra_tower : IsScalarTower A K L := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap A L a = completionFractionMap R ι p (algebraMap A K a)
  rw [completionFractionMap_algebraMap,
    IsScalarTower.algebraMap_apply A B L]
  rfl

/-- The native parameter fraction field is canonically the original rational-function field. -/
def parameterFractionEquiv :
    FractionRing T ≃+* FractionRing (MvPolynomial ι (FractionRing R)) := by
  letI := IsLocalization.originalFractionAlgebra (MvPolynomial ι R)
    (MvPolynomial ι (FractionRing R))
    ((nonZeroDivisors R).map (MvPolynomial.C (σ := ι)))
    (MvPolynomial.coefficient_nonZeroDivisors_le R ι)
  exact (IsLocalization.originalFractionEquiv (MvPolynomial ι R) T
    (parameterIdeal R ι p).primeCompl
    (parameterIdeal R ι p).primeCompl_le_nonZeroDivisors).toRingEquiv.trans
      (MvPolynomial.coefficientFractionEquiv R ι).toRingEquiv.symm

omit [Finite ι] in
/-- The comparison retains the original polynomial image, with its actual coefficient fractions. -/
@[simp] theorem parameterFractionEquiv_polynomial (q : MvPolynomial ι R) :
    parameterFractionEquiv R ι p
        (algebraMap T (FractionRing T) (algebraMap (MvPolynomial ι R) T q)) =
      algebraMap (MvPolynomial ι (FractionRing R))
        (FractionRing (MvPolynomial ι (FractionRing R)))
          (MvPolynomial.map (algebraMap R (FractionRing R)) q) := by
  let M := (parameterIdeal R ι p).primeCompl
  let := IsLocalization.originalFractionAlgebra (MvPolynomial ι R) T M
    (parameterIdeal R ι p).primeCompl_le_nonZeroDivisors
  let e := IsLocalization.originalFractionEquiv (MvPolynomial ι R) T M
    (parameterIdeal R ι p).primeCompl_le_nonZeroDivisors
  let := IsLocalization.originalFractionAlgebra (MvPolynomial ι R)
    (MvPolynomial ι (FractionRing R))
    ((nonZeroDivisors R).map (MvPolynomial.C (σ := ι)))
    (MvPolynomial.coefficient_nonZeroDivisors_le R ι)
  change (MvPolynomial.coefficientFractionEquiv R ι).symm
    (e (algebraMap T (FractionRing T) (algebraMap (MvPolynomial ι R) T q))) = _
  apply (MvPolynomial.coefficientFractionEquiv R ι).injective
  rw [AlgEquiv.apply_symm_apply,
    MvPolynomial.coefficientFractionEquiv_map_algebraMap, e.commutes]
  exact IsLocalization.toOriginalFractionRing_algebraMap _ _ _ _ q

end ParameterLocalization
