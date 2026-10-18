/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.BaseChange
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.PGroupTower
public import Aglib.RingTheory.AdjoinRootNestedBaseChange

/-!
# The actual nested branch sum after p-group scalar descent

Both polynomial norms are expanded by proved base change. Every resulting
branch tower has a lower field embedded in the specified p-group splitting
field, so proved p-group transitivity combines its two norms. No direct/nested
branch bijection or general tower equality is assumed here.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot

universe u

local instance nestedRootFinite {A : Type u} [Field A] (p : MonicIrreducible A) :
    FiniteDimensional A (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance nestedRootCharZero {A : Type u} [Field A] [CharZero A]
    (p : MonicIrreducible A) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap A (AdjoinRoot p.val)).injective

variable {S A B Ω : Type u} [Field S] [CharZero S] [Field A] [CharZero A]
  [Field B] [CharZero B] [Field Ω] [Algebra A B] [Algebra S B] [Algebra S Ω]
  [FiniteDimensional S B] [FiniteDimensional S Ω] [IsGalois S Ω]

/-- Base change followed by the lower norm equals the complete norm sum,
using proved p-group transitivity for each actual upper branch. -/
theorem polynomialNorm_branch_sum_of_pGroup
    (q : MonicIrreducible A)
    [Fintype (IrreducibleBranch (q.val.map (algebraMap A B)))]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[S] Ω)) (g : B →ₐ[S] Ω)
    (n : ℕ) (z : K (AdjoinRoot q.val) n) :
    finiteExtensionNorm S B n (map n (algebraMap A B) (polynomialNorm n q z)) =
      ∑ s : IrreducibleBranch (q.val.map (algebraMap A B)),
        let : FiniteDimensional S (AdjoinRoot s.val.val) :=
          FiniteDimensional.trans S B (AdjoinRoot s.val.val)
        finiteExtensionNorm S (AdjoinRoot s.val.val) n
          (map n (adjoinRootMap (algebraMap A B) q.val s.val.val s.property) z) := by
  classical
  rw [polynomialNorm_restrict_branches, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  let : FiniteDimensional S (AdjoinRoot s.val.val) :=
    FiniteDimensional.trans S B (AdjoinRoot s.val.val)
  exact (finiteExtensionNorm_tower_of_pGroup ℓ hG g n _).symm

end MilnorK
