/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.NestedSum
public import Aglib.RingTheory.AdjoinRootNestedBranches

/-! The complete nested scalar sum equals the restriction of the iterated norm. -/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot

universe u

local instance descentRootFinite {A : Type u} [Field A] (p : MonicIrreducible A) :
    FiniteDimensional A (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance descentRootCharZero {A : Type u} [Field A] [CharZero A]
    (p : MonicIrreducible A) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap A (AdjoinRoot p.val)).injective

attribute [local instance] AdjoinRoot.scalarBranchAlgebra

/-- Every lower scalar branch embeds in the specified p-group ambient; hence
all iterated branch norms combine, with no branch omitted or norm axiom used. -/
theorem polynomialNorm_restrict_nested_of_pGroup
    {k S Ω : Type u} [Field k] [CharZero k] [Field S] [CharZero S] [Field Ω]
    [Algebra k S] [Algebra k Ω] [Algebra S Ω] [IsScalarTower k S Ω]
    [FiniteDimensional S Ω] [IsGalois S Ω]
    (p : MonicIrreducible k) (q : MonicIrreducible (AdjoinRoot p.val))
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k S)))]
    [∀ r : IrreducibleBranch (p.val.map (algebraMap k S)),
      Fintype (IrreducibleBranch
        (q.val.map (algebraMap (AdjoinRoot p.val) (AdjoinRoot r.val.val))))]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[S] Ω))
    (hsplit : (p.val.map (algebraMap k Ω)).Splits)
    (n : ℕ) (z : K (AdjoinRoot q.val) n) :
    map n (algebraMap k S) (polynomialNorm n p (polynomialNorm n q z)) =
      ∑ u : NestedScalarBranch (S := S) p.val q.val,
        let : FiniteDimensional S (AdjoinRoot u.2.val.val) :=
          FiniteDimensional.trans S (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val)
        finiteExtensionNorm S (AdjoinRoot u.2.val.val) n
          (map n (adjoinRootMap
            (algebraMap (AdjoinRoot p.val) (AdjoinRoot u.1.val.val))
            q.val u.2.val.val u.2.property) z) := by
  classical
  refine (polynomialNorm_restrict_branches (S := S) p n (polynomialNorm n q z)).trans ?_
  refine Eq.trans ?_ (Fintype.sum_sigma _).symm
  apply Finset.sum_congr rfl
  intro r _
  let g : AdjoinRoot r.val.val →ₐ[S] Ω := Classical.choice
    (nonempty_algHom_branch_of_splits
      (L := S) (Ω := Ω) p.val p.property.1.ne_zero hsplit r).1
  exact polynomialNorm_branch_sum_of_pGroup q ℓ hG g n z

end MilnorK
