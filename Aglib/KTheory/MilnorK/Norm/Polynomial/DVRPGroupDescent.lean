/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteBranchSum
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRWeightedBaseChange
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRRestrictionKernel
public import Aglib.RingTheory.AdjoinRootTensorBranchProduct

/-!
# Actual degree annihilation from all local p-group branches

The two independently proved full branch sums coincide. Their difference is
killed after ramification-weighted restriction; actual residue projection and
the finite DVR degree formula then give the fraction-field degree annihilator.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue AdjoinRoot IsLocalRing
open scoped TensorProduct

attribute [local instance] MilnorK.rootFinite

universe u

/-- The restricted residue of the original norm is the full upper branch sum,
with each original vertical ramification exponent visible. -/
theorem degree_smul_normResidue_defect_eq_zero_of_pGroup_branches
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L] [FiniteDimensional F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Module.Finite R T] [Module.IsTorsionFree R T]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L] [IsIntegralClosure T R L]
    (p : MonicIrreducible F)
    [Algebra S (AdjoinRoot p.val)] [IsFractionRing S (AdjoinRoot p.val)]
    [Algebra R S] [IsScalarTower R S (AdjoinRoot p.val)]
    [Module.Finite R S] [Module.IsTorsionFree R S] [IsIntegralClosure S R (AdjoinRoot p.val)]
    [IsLocalHom (algebraMap R S)]
    (U : IrreducibleBranch (p.val.map (algebraMap F L)) → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
    [∀ r, Module.IsTorsionFree T (U r)]
    [∀ r, Algebra S (U r)] [∀ r, Algebra R (U r)]
    [∀ r, IsScalarTower R S (U r)] [∀ r, IsScalarTower R T (U r)]
    [∀ r, IsLocalHom (algebraMap S (U r))] [∀ r, IsLocalHom (algebraMap R (U r))]
    [∀ r, IsLocalHom (algebraMap T (U r))]
    [∀ r, Algebra (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsScalarTower T (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsFractionRing (U r) (AdjoinRoot r.val.val)]
    [∀ r, IsIntegralClosure (U r) T (AdjoinRoot r.val.val)]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : IrreducibleBranch (p.val.map (algebraMap F L)),
      AdjoinRoot r.val.val →ₐ[L] Ω)
    (hj : ∀ r s, adjoinRootMap (algebraMap F L) p.val r.val.val r.property
      (algebraMap S (AdjoinRoot p.val) s) =
        algebraMap (U r) (AdjoinRoot r.val.val) (algebraMap S (U r) s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w z : ∀ r, (U r)ˣ) (b c : IrreducibleBranch (p.val.map (algebraMap F L)) → ℕ)
    (hb : ∀ r, algebraMap S (U r) ϖ = (w r : U r) * ρ r ^ b r)
    (hc : ∀ r, algebraMap T (U r) τ = (z r : U r) * ρ r ^ c r)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    Module.finrank F L •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        finiteExtensionNorm (ResidueField R) (ResidueField S) n
          (DVR.residue S (AdjoinRoot p.val) n x)) = 0 := by
  classical
  let : Finite (IrreducibleBranch (p.val.map (algebraMap F L))) :=
    finite_irreducibleBranch _ (p.property.1.map _)
  let : Fintype (IrreducibleBranch (p.val.map (algebraMap F L))) := Fintype.ofFinite _
  let B := Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
  obtain ⟨θ, hθ⟩ := IsLocalRing.residue_surjective B.gen
  have hcoordinates (r : IrreducibleBranch (p.val.map (algebraMap F L))) :
      algebraMap (U r) (AdjoinRoot r.val.val) (algebraMap S (U r) θ) =
        tensorBranchProductEquiv p.val p.property.1 p.property.2.separable
          (1 ⊗ₜ[F] (algebraMap S (AdjoinRoot p.val) θ)) r := by
    rw [tensorBranchProductEquiv_tmul_one]
    exact (hj r θ).symm
  have hsum := ramification_restrict_residue_polynomialNorm_eq_branch_sum
    R S T p U Ω ℓ hG g (fun r => algebraMap S (U r)) hj
    hπ hϖ hτ ρ hρ v a ha w b hb n x
  have hweighted := residue_norm_weighted_baseChange R F S (AdjoinRoot p.val) T L
    (fun r : IrreducibleBranch (p.val.map (algebraMap F L)) => AdjoinRoot r.val.val) U
    (tensorBranchProductEquiv p.val p.property.1 p.property.2.separable) θ hcoordinates
    hπ hϖ hτ u e he v a ha B hθ.symm ρ hρ w z b c hb hc n
    (DVR.residue S (AdjoinRoot p.val) n x)
  have hres : algebraMap (ResidueField R) (ResidueField T) =
      ResidueField.map (algebraMap R T) := by
    ext t
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
    rfl
  apply degree_smul_eq_zero_of_ramified_residue_restrict R T F L hπ hτ v a ha n
  rw [map_sub, smul_sub, hres, hsum]
  rw [← hres, hweighted, sub_self]

end MilnorK.PolynomialNorm
