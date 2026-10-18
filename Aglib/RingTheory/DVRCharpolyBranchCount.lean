/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralTensorCharpolyProduct
public import Aglib.RingTheory.PolynomialPowerFactorCount
public import Aglib.FieldTheory.AdjoinRootMinpolyDegree
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Residue-branch multiplicities from actual tensor characteristic polynomials

The full generic tensor decomposition first gives the original integral
characteristic-polynomial product. Reduction and unique factorization then
compute every residue-branch multiplicity. No factorization or count is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped TensorProduct

namespace Algebra

variable (R F S E T L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type*} [Fintype ι] (D U : ι → Type*)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [CharZero (ResidueField R)] [DecidableEq (ResidueField T)]

/-- The full generic tensor decomposition forces the sum of ramification times
relative residue degree over each actual minimal-polynomial branch to be the
original ramification exponent. -/
theorem sum_residue_branch_degrees_eq_ramification
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S) (c : ∀ i, U i)
    (hc : ∀ i, algebraMap (U i) (D i) (c i) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b)
    {τ : T} (hτ : Irreducible τ) (ω : ∀ i, U i)
    (hω : ∀ i, Irreducible (ω i)) (v : ∀ i, (U i)ˣ) (d : ι → ℕ)
    (hd : ∀ i, algebraMap T (U i) τ = (v i : U i) * ω i ^ d i)
    (q : AdjoinRoot.IrreducibleBranch
      ((minpoly (ResidueField R) (residue S b)).map
        (algebraMap (ResidueField R) (ResidueField T)))) :
    (∑ i, if minpoly (ResidueField T) (residue (U i) (c i)) = q.val.val then
      d i * Module.finrank
        (IntermediateField.adjoin (ResidueField T) {residue (U i) (c i)})
        (ResidueField (U i)) else 0) = e := by
  let : CharZero (ResidueField T) :=
    charZero_of_injective_algebraMap
      (algebraMap (ResidueField R) (ResidueField T)).injective
  let P := (minpoly (ResidueField R) (residue S b)).map
    (algebraMap (ResidueField R) (ResidueField T))
  let p := fun i => minpoly (ResidueField T) (residue (U i) (c i))
  let w := fun i => d i * Module.finrank
    (IntermediateField.adjoin (ResidueField T) {residue (U i) (c i)})
    (ResidueField (U i))
  have hint := map_charpoly_lmul_eq_prod_integralClosure R F S E T L D U ε b c hc
  have hprod : P ^ e = ∏ i, p i ^ w i := calc
    P ^ e = ((lmul R S b).charpoly.map (residue R)).map
        (algebraMap (ResidueField R) (ResidueField T)) := by
      rw [residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis R S hπ hϖ u e he b B hB,
        Polynomial.map_pow]
    _ = ((lmul R S b).charpoly.map (algebraMap R T)).map (residue T) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    _ = (∏ i, (lmul T (U i) (c i)).charpoly).map (residue T) := by rw [hint]
    _ = ∏ i, p i ^ w i := by
      rw [Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact residue_charpoly_lmul_eq_minpoly_pow T (U i) hτ (hω i) (v i) (d i) (hd i) (c i)
  have hP : P.Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ResidueField R) (residue S b))).map _
  have hPsq : Squarefree P :=
    ((minpoly.irreducible
      (Algebra.IsIntegral.isIntegral (R := ResidueField R) (residue S b))).separable.map).squarefree
  have hp : ∀ i, (p i).Monic ∧ Irreducible (p i) := fun i =>
    ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (R := ResidueField T) (residue (U i) (c i))),
      minpoly.irreducible
        (Algebra.IsIntegral.isIntegral (R := ResidueField T) (residue (U i) (c i)))⟩
  exact Polynomial.sum_weights_eq_of_prod_eq_squarefree_pow P hP hPsq p hp w e hprod.symm q

end Algebra
