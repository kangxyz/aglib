/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Complete
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRResidueEquiv

/-!
# Actual finite norms in the general complete-DVR square

The proved general complete-DVR square is expressed using the actual residue field and
its presentation-independent finite norm. Completeness and residue
characteristic zero remain explicit.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue IsLocalRing PolynomialNorm
open IsDiscreteValuationRing.CompleteExtension

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- The complete square with both norms on the actual original fields. -/
theorem residue_finiteExtensionNorm_complete_root
    (p : MonicIrreducible F) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    let _ := integralClosure_residue_finite R F (AdjoinRoot p.val)
    DVR.residue R F n (finiteExtensionNorm F (AdjoinRoot p.val) (n + 1) x) =
      finiteExtensionNorm (ResidueField R)
        (ResidueField (integralClosure R (AdjoinRoot p.val))) n
        (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x) := by
  dsimp only
  let E := AdjoinRoot p.val
  let S := integralClosure R E
  let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let _ := integralClosure_isDiscreteValuationRing R F E
  let _ := integralClosure_isLocalHom R F E
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let _ := integralClosure_residue_finite R F E
  rw [finiteExtensionNorm_adjoinRoot]
  exact residue_polynomialNorm_complete R F p n x

/-- Every actual finite extension satisfies the local square in
any specified finite DVR integral closure of the original complete base. -/
theorem residue_finiteExtensionNorm_complete
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra R E] [IsScalarTower R F E]
    (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) := by
  let p := finiteNormPolynomial F E
  let ε := finiteNormPresentation F E
  let A := AdjoinRoot p.val
  let B := integralClosure R A
  let C := integralClosure R E
  let : FiniteDimensional F A := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let : IsDiscreteValuationRing B := integralClosure_isDiscreteValuationRing R F A
  let : IsLocalHom (algebraMap R B) := integralClosure_isLocalHom R F A
  let : IsFractionRing B A :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F A B
  let : Module.Finite (ResidueField R) (ResidueField B) :=
    integralClosure_residue_finite R F A
  let j : B ≃ₐ[R] S := (CompleteDVRResidueEquiv.closureEquiv R F ε).trans
    (IsIntegralClosure.equiv R C E S)
  have hj (b : B) : ε (algebraMap B A b) = algebraMap S E (j b) := by
    dsimp only [j, AlgEquiv.trans_apply]
    rw [IsIntegralClosure.algebraMap_equiv]
    rfl
  exact residue_finiteExtensionNorm_of_equiv j ε hj n
    (residue_finiteExtensionNorm_complete_root R F p n) x

end MilnorK
