/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower

/-!
# Weighted refinement of actual scalar branches

This is the norm-theoretic consumer of the local ramification fiber count.
The integer weight identity remains explicit; no residue compatibility or
norm equality is assumed. Every term retains its literal quotient map.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue PolynomialNorm Polynomial.LocalResidue AdjoinRoot

attribute [local instance] rootFinite

universe u v

/-- The literal ramification squares convert horizontal degree weights into
the vertical weights used by residue restriction. -/
theorem ramification_fiber_weight_conversion
    {ι : Type*} [Fintype ι] (e a : ℕ) (he : 0 < e) (b c d : ι → ℕ)
    (hsquare : ∀ i, e * b i = a * c i)
    (hcount : ∑ i, c i * d i = e) : ∑ i, b i * d i = a := by
  apply Nat.eq_of_mul_eq_mul_left he
  calc
    e * ∑ i, b i * d i = ∑ i, (e * b i) * d i := by
      rw [Finset.mul_sum]
      simp only [Nat.mul_assoc]
    _ = ∑ i, (a * c i) * d i := by simp_rw [hsquare]
    _ = a * ∑ i, c i * d i := by
      rw [Finset.mul_sum]
      simp only [Nat.mul_assoc]
    _ = e * a := by rw [hcount, Nat.mul_comm]

/-- Refining each residue scalar branch by finite fields preserves the norm
sum with the exact degree-weighted multiplicity. -/
theorem polynomialNorm_restrict_weighted_branches
    {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Algebra k L]
    (p : MonicIrreducible k)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k L)))]
    (I : IrreducibleBranch (p.val.map (algebraMap k L)) → Type v) [∀ j, Fintype (I j)]
    (D : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → Type u)
    [∀ j i, Field (D j i)] [∀ j i, Algebra L (D j i)]
    [∀ j i, Algebra (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, IsScalarTower L (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, FiniteDimensional L (D j i)]
    [∀ j i, FiniteDimensional (AdjoinRoot j.val.val) (D j i)]
    (b : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → ℕ)
    (a : ℕ)
    (hcount : ∀ j, ∑ i, b j i * Module.finrank (AdjoinRoot j.val.val) (D j i) = a)
    (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    a • map n (algebraMap k L) (polynomialNorm n p x) =
      ∑ j, ∑ i, b j i • finiteExtensionNorm L (D j i) n
        (map n ((algebraMap (AdjoinRoot j.val.val) (D j i)).comp
          (adjoinRootMap (algebraMap k L) p.val j.val.val j.property)) x) := by
  classical
  rw [polynomialNorm_restrict_branches, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let : CharZero (AdjoinRoot j.val.val) :=
    charZero_of_injective_algebraMap (algebraMap L (AdjoinRoot j.val.val)).injective
  symm
  calc
    _ = ∑ i, (b j i * Module.finrank (AdjoinRoot j.val.val) (D j i)) •
        finiteExtensionNorm L (AdjoinRoot j.val.val) n
          (map n (adjoinRootMap (algebraMap k L) p.val j.val.val j.property) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_comp, LinearMap.comp_apply,
        finiteExtensionNorm_tower (AdjoinRoot j.val.val) (D j i),
        finiteExtensionNorm_map_constants, map_smul]
      simp only [natCast_zsmul, smul_smul]
    _ = _ := by rw [← Finset.sum_smul, hcount]

/-- The same weighted sum retains any original residue-field presentation. -/
theorem finiteExtensionNorm_restrict_weighted_presentation
    {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Algebra k L]
    (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E]
    (p : MonicIrreducible k) (ε : AdjoinRoot p.val ≃ₐ[k] E)
    [Fintype (IrreducibleBranch (p.val.map (algebraMap k L)))]
    (I : IrreducibleBranch (p.val.map (algebraMap k L)) → Type v) [∀ j, Fintype (I j)]
    (D : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → Type u)
    [∀ j i, Field (D j i)] [∀ j i, Algebra L (D j i)]
    [∀ j i, Algebra (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, IsScalarTower L (AdjoinRoot j.val.val) (D j i)]
    [∀ j i, FiniteDimensional L (D j i)]
    [∀ j i, FiniteDimensional (AdjoinRoot j.val.val) (D j i)]
    (b : (j : IrreducibleBranch (p.val.map (algebraMap k L))) → I j → ℕ)
    (a : ℕ)
    (hcount : ∀ j, ∑ i, b j i * Module.finrank (AdjoinRoot j.val.val) (D j i) = a)
    (n : ℕ) (x : K E n) :
    a • map n (algebraMap k L) (finiteExtensionNorm k E n x) =
      ∑ j, ∑ i, b j i • finiteExtensionNorm L (D j i) n
        (map n ((algebraMap (AdjoinRoot j.val.val) (D j i)).comp
          ((adjoinRootMap (algebraMap k L) p.val j.val.val j.property).comp
            ε.symm.toRingHom)) x) := by
  rw [finiteExtensionNorm_eq_presentation k E n p ε, LinearMap.comp_apply]
  have h := polynomialNorm_restrict_weighted_branches p I D b a hcount n
    (map n ε.symm.toRingHom x)
  simpa only [map_comp, LinearMap.comp_apply] using h

end MilnorK
