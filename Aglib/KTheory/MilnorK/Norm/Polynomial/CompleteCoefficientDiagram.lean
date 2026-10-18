/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CoprimeRootSquare
public import Aglib.RingTheory.CompleteDVRIntegralClosureTower

/-!
# The actual complete-DVR coefficient diagram

The upper field is the literal root field of the irreducible coefficient
polynomial. Its old-root algebra is the coefficient map, and both upper ring
maps are the restrictions to the actual integral closures. The complete-DVR
hypothesis is not weakened to a Henselian transfer assumption.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm.CompleteCoefficientDiagram

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open IsDiscreteValuationRing.IntegralClosureTower IsDiscreteValuationRing.CompleteExtension

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
  (p : MonicIrreducible F) (hcop : p.val.natDegree.Coprime (Module.finrank F L))

/-- The old root acts through the literal coefficient map. -/
@[instance_reducible] def coefficientAlgebra :
    Algebra (AdjoinRoot p.val) (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val) :=
  (AdjoinRoot.coefficientMap p.val).toRingHom.toAlgebra

attribute [local instance] coefficientAlgebra

/-- The coefficient map fixes the original coefficient field. -/
instance coefficientTower :
    IsScalarTower F (AdjoinRoot p.val)
      (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val) :=
  IsScalarTower.of_algebraMap_eq fun x => (AdjoinRoot.coefficientMap p.val).commutes x |>.symm

/-- This is the exact map used in singleton polynomial norm base change. -/
theorem coefficient_algebraMap_eq :
    algebraMap (AdjoinRoot p.val) (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val) =
      adjoinRootMap (algebraMap F L) p.val
        (coprimeCoefficientPolynomial p hcop).val dvd_rfl := by
  let : Fact (Irreducible (p.val.map (algebraMap F L))) :=
    ⟨(coprimeCoefficientPolynomial p hcop).property.2⟩
  exact (adjoinRootMap_eq_coefficientMap (L := L) p.val).symm

variable (R : Type*) [CommRing R] [Algebra R F] [Algebra R L] [IsScalarTower R F L]

/-- Compatibility with the original valuation ring follows through its fraction field. -/
instance baseCoefficientTower :
    IsScalarTower R (AdjoinRoot p.val)
      (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [IsScalarTower.algebraMap_apply R F (AdjoinRoot p.val),
    ← IsScalarTower.algebraMap_apply F (AdjoinRoot p.val)
      (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val),
    ← IsScalarTower.algebraMap_apply R F
      (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val)]

end MilnorK.PolynomialNorm.CompleteCoefficientDiagram
