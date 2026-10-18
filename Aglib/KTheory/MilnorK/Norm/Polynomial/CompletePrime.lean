/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteCoprimeDescent

/-!
# All-class prime-normal norm-residue compatibility over a complete DVR

Finite classwise coprime mixed generation supplies the actual coefficient
extension. Complete integral closures instantiate the finite DVR square, whose
two proven annihilators kill the norm-residue defect. The original norm and
residue presentation maps remain literal. Completeness, characteristic zero of
the residue field, and normal prime field degree remain explicit; no global
norm tower, arbitrary-DVR reduction, or curve reciprocity is asserted.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

universe u

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- Every original Milnor class satisfies the prime-normal polynomial norm-residue
square over a complete DVR. The extension DVR is the actual integral closure,
with all its local, fraction-field and DVR structure proved rather than assumed. -/
theorem residue_polynomialNorm_complete_prime
    (p : MonicIrreducible F) [Normal F (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (q : MonicIrreducible (ResidueField R)) :
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    ∀ ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField (integralClosure R (AdjoinRoot p.val)),
      DVR.residue R F n (polynomialNorm (n + 1) p x) =
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x)) := by
  obtain ⟨L, hL, hFL, hfinite, _, hcop, pL, hpL, hdiv, c, hc⟩ :=
    exists_finite_coprime_mixed_expansion p hp n x
  let := hfinite
  let : Algebra R L := ((algebraMap F L).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have heq : pL = coprimeCoefficientPolynomial p hcop := Subtype.ext hpL
  subst pL
  have hx : map (n + 1) (adjoinRootMap (algebraMap F L) p.val
      (coprimeCoefficientPolynomial p hcop).val dvd_rfl) x ∈
      mixedSpan (algebraMap L (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val)) n := by
    rw [← hc]
    exact Submodule.sum_mem _ fun ab _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨ab.1, ab.2, rfl⟩)
  exact residue_polynomialNorm_of_complete_coprime_mixed R F L p hp hcop n x hx q

end MilnorK.PolynomialNorm
