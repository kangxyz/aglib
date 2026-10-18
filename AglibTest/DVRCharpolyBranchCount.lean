/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRCharpolyBranchCount
public import Lean.Util.CollectAxioms

/-! Full actual tensor branch count, with no characteristic-polynomial product premise. -/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped TensorProduct

namespace AglibTest.DVRCharpolyBranchCount

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

theorem actualTensorResidueBranchCount
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
        (ResidueField (U i)) else 0) = e :=
  Algebra.sum_residue_branch_degrees_eq_ramification R F S E T L D U
    ε b c hc hπ hϖ u e he B hB hτ ω hω v d hd q

open Lean in
run_cmd do
  for name in #[``Polynomial.count_normalizedFactors_prod_irreducible_pow,
      ``Polynomial.sum_weights_eq_of_prod_eq_squarefree_pow,
      ``Algebra.map_charpoly_lmul_eq_prod_tensor,
      ``Algebra.map_charpoly_lmul_eq_prod_integralClosure,
      ``Algebra.residue_charpoly_lmul_eq_minpoly_pow,
      ``AdjoinRoot.finrank_adjoin_eq_of_minpoly_eq,
      ``Algebra.sum_residue_branch_degrees_eq_ramification,
      ``actualTensorResidueBranchCount] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual tensor-to-residue branch multiplicities use only standard foundations."

end AglibTest.DVRCharpolyBranchCount
