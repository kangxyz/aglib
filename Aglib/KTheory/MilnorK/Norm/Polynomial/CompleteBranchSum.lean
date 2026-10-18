/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompleteRamifiedBranch
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.WeightedBranches

/-!
# The full ramification-weighted coefficient branch sum

Scalar base change of the original polynomial norm and the proved local p-group
squares give the entire weighted residue sum. All uniformizer equations and
literal quotient maps are retained. No weighted fiber count is assumed here.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue AdjoinRoot IsLocalRing

attribute [local instance] MilnorK.rootFinite

universe u

/-- The restricted residue of the original norm is the full upper branch sum,
with each original vertical ramification exponent visible. -/
theorem ramification_restrict_residue_polynomialNorm_eq_branch_sum
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L]
    (p : MonicIrreducible F)
    [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
    [Fintype (IrreducibleBranch (p.val.map (algebraMap F L)))]
    (U : IrreducibleBranch (p.val.map (algebraMap F L)) → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
    [∀ r, IsLocalHom (algebraMap T (U r))]
    [∀ r, Algebra (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsScalarTower T (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsFractionRing (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsIntegralClosure (U r) T (AdjoinRoot r.val.val)]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : IrreducibleBranch (p.val.map (algebraMap F L)),
      AdjoinRoot r.val.val →ₐ[L] Ω)
    (j : ∀ r, S →+* U r) [∀ r, IsLocalHom (j r)]
    (hj : ∀ r s, adjoinRootMap (algebraMap F L) p.val r.val.val r.property
      (algebraMap S (AdjoinRoot p.val) s) =
        algebraMap (U r) (AdjoinRoot r.val.val) (j r s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w : ∀ r, (U r)ˣ) (b : IrreducibleBranch (p.val.map (algebraMap F L)) → ℕ)
    (hb : ∀ r, j r ϖ = (w r : U r) * ρ r ^ b r)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    a • map n (ResidueField.map (algebraMap R T))
      (DVR.residue R F n (polynomialNorm (n + 1) p x)) =
      ∑ r, b r • finiteExtensionNorm (ResidueField T) (ResidueField (U r)) n
        (map n (ResidueField.map (j r)) (DVR.residue S (AdjoinRoot p.val) n x)) := by
  classical
  have hc (r : R) : algebraMap F L (algebraMap R F r) =
      algebraMap T L (algebraMap R T r) := by
    rw [← IsScalarTower.algebraMap_apply R F L, ← IsScalarTower.algebraMap_apply R T L]
  rw [← natCast_zsmul, ← DVR.residue_ramified_restrict_apply
    (algebraMap R T) (algebraMap F L) hc hπ hτ v a ha,
    polynomialNorm_restrict_branches, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  let : CharZero (AdjoinRoot r.val.val) :=
    charZero_of_injective_algebraMap (algebraMap L (AdjoinRoot r.val.val)).injective
  exact residue_norm_restrict_complete_pGroup_branch S T (U r) (AdjoinRoot p.val)
    L (AdjoinRoot r.val.val) Ω ℓ hG (g r) (j r)
    (adjoinRootMap (algebraMap F L) p.val r.val.val r.property) (hj r)
    hϖ (hρ r) (w r) (b r) (hb r) n x

end MilnorK.PolynomialNorm
