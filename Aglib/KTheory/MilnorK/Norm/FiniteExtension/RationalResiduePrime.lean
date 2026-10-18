/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalTower
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFinitePrime

/-!
# The actual residue-field norm in the prime rational square

Tensor matching is consumed into the original residue extension, whose scalar
map is exactly the quotient map induced by coefficient inclusion. This is the
form needed to compose finite-place squares using general norm transitivity.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra

universe u

local instance residueRootFinite {A : Type u} [Field A] (p : MonicIrreducible A) :
    FiniteDimensional A (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance residueRootCharZero {A : Type u} [Field A] [CharZero A]
    (p : MonicIrreducible A) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap A (AdjoinRoot p.val)).injective

/-- The actual finite residue extension lies over the original coefficient map. -/
theorem finiteDimensional_scalarBranch_residue
    {k L : Type u} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (h : MonicIrreducible k)
    (r : IrreducibleBranch (h.val.map (algebraMap k L))) :
    FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) := by
  let : FiniteDimensional k (AdjoinRoot r.val.val) :=
    FiniteDimensional.trans k L (AdjoinRoot r.val.val)
  let : IsScalarTower k (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
    scalarBranchBaseTower h.val r
  exact FiniteDimensional.right k (AdjoinRoot h.val) (AdjoinRoot r.val.val)

/-- The matched branch equivalence preserves the actual lower residue field. -/
def tensorBranchResidueAlgEquiv
    {k : Type u} [Field k] (p h : MonicIrreducible k)
    (r : IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val)))) :
    AdjoinRoot r.val.val ≃ₐ[AdjoinRoot h.val]
      AdjoinRoot (tensorSwapBranchEquiv p.val h.val r).val.val :=
  { tensorSwapBranchRingEquiv p.val h.val r with
    commutes' := tensorSwapBranchRingEquiv_adjoinRootMap p.val h.val r }

/-- The tensor-matched polynomial norm is the norm of the original residue
field extension, not a second presentation-dependent transfer. -/
theorem tensorBranch_polynomialNorm_eq_finiteExtensionNorm
    {k : Type u} [Field k] [CharZero k] (p h : MonicIrreducible k)
    (r : IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (n : ℕ) (z : K (AdjoinRoot r.val.val) n) :
    let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
      finiteDimensional_scalarBranch_residue h r
    polynomialNorm n (tensorSwapBranchEquiv p.val h.val r).val
      (map n (tensorSwapBranchRingEquiv p.val h.val r).toRingHom z) =
        finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n z := by
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
    finiteDimensional_scalarBranch_residue h r
  rw [← finiteExtensionNorm_adjoinRoot (tensorSwapBranchEquiv p.val h.val r).val n]
  exact finiteExtensionNorm_map_algEquiv (tensorBranchResidueAlgEquiv p h r) n z

local instance primeRationalFinite {k E : Type u} [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] : FiniteDimensional (RatFunc k) (RatFunc E) :=
  FiniteDimensional.of_finrank_pos (by
    rw [RatFunc.finrank_ratFunc_ratFunc]
    exact Module.finrank_pos)

/-- The actual normal-prime rational finite-place square, now expressed solely
with norms of the original finite residue extensions and all their branches. -/
theorem residueAt_finiteExtensionNorm_rational_prime_root
    {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)
    [Normal k (AdjoinRoot p.val)] (hp : p.val.natDegree.Prime)
    (h : MonicIrreducible k)
    [Fintype (IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))]
    (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt h.val n
      (finiteExtensionNorm (RatFunc k) (RatFunc (AdjoinRoot p.val)) (n + 1) x) =
      ∑ r : IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))),
        let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
          finiteDimensional_scalarBranch_residue h r
        finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
          (residueAt r.val.val n x) := by
  classical
  rw [← rationalFunctionNorm_eq_finiteExtensionNorm p (n + 1)]
  refine (residueAt_rationalFunctionNorm_prime p hp h n x).trans ?_
  apply Fintype.sum_equiv (placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h)
  intro r
  exact tensorBranch_polynomialNorm_eq_finiteExtensionNorm p h
    (placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h r) n _

end MilnorK
