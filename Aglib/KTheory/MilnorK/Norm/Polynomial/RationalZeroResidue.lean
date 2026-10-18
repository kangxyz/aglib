/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalZeroResiduePGroup
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalBaseChange

/-!
# The general normalized rational X norm-residue square

Restriction to every Sylow fixed field expands the rational norm into all
actual coefficient branches. Each branch embeds in the p-group splitting
ambient and satisfies the proved X-square. The original difference vanishes
by joint restriction detection. No prime, normality, or residue-law premise
remains in the resulting all-class polynomial norm theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra
  MilnorK.zeroRootFinite MilnorK.zeroRationalFinite

local instance zeroRootCharZero {k : Type*} [Field k] [CharZero k]
    (p : MonicIrreducible k) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

universe u

/-- The actual p-group X-square in the original polynomial presentation. -/
theorem rationalZeroResidue_rationalFunctionNorm_of_pGroup
    {k Ω : Type u} [Field k] [CharZero k] [Field Ω]
    [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
    (p : MonicIrreducible k) (ℓ : ℕ) [Fact ℓ.Prime]
    (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω)) (g : AdjoinRoot p.val →ₐ[k] Ω)
    (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    rationalZeroResidue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (rationalZeroResidue (AdjoinRoot p.val) n x) := by
  rw [rationalFunctionNorm_eq_finiteExtensionNorm,
    ← finiteExtensionNorm_adjoinRoot p n]
  exact rationalZeroResidue_finiteExtensionNorm_of_pGroup ℓ hG g n x

/-- Every actual polynomial presentation satisfies the normalized rational
X norm-residue square in all degrees over characteristic-zero fields. -/
theorem rationalZeroResidue_rationalFunctionNorm
    {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    rationalZeroResidue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (rationalZeroResidue (AdjoinRoot p.val) n x) := by
  classical
  let Ω := p.val.SplittingField
  let : IsGalois k Ω := ⟨⟩
  apply eq_of_sylow_restrictions k Ω n
  intro ℓ hℓ
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let P : Sylow ℓ (Ω ≃ₐ[k] Ω) := Classical.arbitrary _
  let S := IntermediateField.fixedField (P : Subgroup (Ω ≃ₐ[k] Ω))
  refine ⟨P, ?_⟩
  change map n (algebraMap k S)
      (rationalZeroResidue k n (rationalFunctionNorm (n + 1) p x)) =
    map n (algebraMap k S) (polynomialNorm n p (rationalZeroResidue (AdjoinRoot p.val) n x))
  rw [← rationalZeroResidue_restrict (algebraMap k S) n
    (rationalFunctionNorm (n + 1) p x), rationalFunctionNorm_restrict,
    map_sum, polynomialNorm_restrict]
  apply Finset.sum_congr rfl
  intro q _
  let qb : IrreducibleBranch (p.val.map (algebraMap k S)) :=
    ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩
  let g : AdjoinRoot q.val.val →ₐ[S] Ω := Classical.choice
    (nonempty_algHom_branch_of_splits (L := S) (Ω := Ω)
      p.val p.property.1.ne_zero (SplittingField.splits p.val) qb).1
  rw [rationalZeroResidue_rationalFunctionNorm_of_pGroup q.val ℓ
    (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ P) g]
  rw [rationalZeroResidue_restrict]

end MilnorK.PolynomialNorm
