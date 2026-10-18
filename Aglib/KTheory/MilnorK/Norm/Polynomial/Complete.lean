/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompletePGroupDescent
public import Aglib.KTheory.MilnorK.RestrictionSylow

/-!
# General complete-DVR norm-residue compatibility

Actual Sylow coefficient extensions annihilate the local defect by coprime
field degrees. All upper branches and ramification factors are supplied by
the proved complete integral-closure descent theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

universe u

/-- Every polynomial norm satisfies the complete-DVR residue square in all
Milnor degrees. Residue characteristic zero and completeness are explicit. -/
theorem residue_polynomialNorm_complete
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    (p : MonicIrreducible F) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    let _ := p.property.1.finite_adjoinRoot
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    let _ := integralClosure_residue_finite R F (AdjoinRoot p.val)
    DVR.residue R F n (polynomialNorm (n + 1) p x) =
      finiteExtensionNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot p.val))) n
          (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x) := by
  classical
  dsimp only
  apply sub_eq_zero.mp
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨ℓ, hℓ, hdiv⟩ := Nat.exists_prime_and_dvd h
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let Ω := p.val.SplittingField
  let : IsGalois F Ω := ⟨⟩
  let P : Sylow ℓ (Ω ≃ₐ[F] Ω) := Classical.arbitrary _
  let L := IntermediateField.fixedField (P : Subgroup (Ω ≃ₐ[F] Ω))
  let : Algebra R L := (algebraMap F L).comp (algebraMap R F) |>.toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g (r : IrreducibleBranch (p.val.map (algebraMap F L))) :
      AdjoinRoot r.val.val →ₐ[L] Ω := Classical.choice
    (nonempty_algHom_branch_of_splits (L := L) (Ω := Ω)
      p.val p.property.1.ne_zero (SplittingField.splits p.val) r).1
  have hz := degree_smul_normResidue_defect_complete_of_pGroup_branches
    R F L p Ω ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ P) g n x
  exact (hℓ.coprime_iff_not_dvd.mp
    (IntermediateField.coprime_finrank_sylow_fixedField ℓ P))
    (hdiv.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz))

end MilnorK.PolynomialNorm
