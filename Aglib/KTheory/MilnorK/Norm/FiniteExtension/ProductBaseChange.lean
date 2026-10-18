/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.BaseChange
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv
public import Aglib.RingTheory.AdjoinRootFieldProductBranches

/-!
# Norm base change through actual field product coordinates

A supplied actual algebra decomposition reindexes the proved polynomial branch
formula. Each field norm is identified by the entire original coordinate map.
This will consume the fraction-field decomposition of completed valuation rings.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot

variable {k L ι : Type*} [Field k] [CharZero k] [Field L] [CharZero L]
  [Algebra k L] [Fintype ι]
  (D : ι → Type*) [∀ i, Field (D i)] [∀ i, Algebra L (D i)]
  [∀ i, FiniteDimensional L (D i)]

/-- The full actual field product gives the literal sum of original coordinate norms. -/
theorem polynomialNorm_restrict_fieldProduct (p : MonicIrreducible k)
    (e : AdjoinRoot (p.val.map (algebraMap k L)) ≃ₐ[L] ∀ i, D i)
    (n : ℕ) (x : K (AdjoinRoot p.val) n) :
    map n (algebraMap k L) (polynomialNorm n p x) =
      ∑ i, finiteExtensionNorm L (D i) n
        (map n (((Pi.evalRingHom D i).comp e.toRingHom).comp
          (scalarMap (algebraMap k L) p.val)) x) := by
  classical
  let : Finite (IrreducibleBranch (p.val.map (algebraMap k L))) :=
    finite_irreducibleBranch _ (p.property.1.map _)
  let : Fintype (IrreducibleBranch (p.val.map (algebraMap k L))) := Fintype.ofFinite _
  let hp := (p.property.1.map (algebraMap k L)).ne_zero
  let : ∀ r : IrreducibleBranch (p.val.map (algebraMap k L)),
      FiniteDimensional L (AdjoinRoot r.val.val) := fun r => r.val.property.1.finite_adjoinRoot
  let β := fieldProductBranchEquiv D _ hp e.toRingEquiv
  rw [polynomialNorm_restrict_branches]
  trans ∑ i, finiteExtensionNorm L (AdjoinRoot (β i).val.val) n
    (map n (adjoinRootMap (algebraMap k L) p.val (β i).val.val (β i).property) x)
  · exact (Fintype.sum_equiv β _ _ (fun _ => rfl)).symm
  · apply Finset.sum_congr rfl
    intro i _
    let : FiniteDimensional L (AdjoinRoot (β i).val.val) :=
      (β i).val.property.1.finite_adjoinRoot
    let η := fieldProductBranchAlgEquiv D _ hp e i
    have hmap : η.toRingHom.comp
        (adjoinRootMap (algebraMap k L) p.val (β i).val.val (β i).property) =
          ((Pi.evalRingHom D i).comp e.toRingHom).comp
            (scalarMap (algebraMap k L) p.val) := by
      apply RingHom.ext
      intro a
      have h := fieldProductBranchRingEquiv_divisorMap D _ hp e.toRingEquiv i
        (scalarMap (algebraMap k L) p.val a)
      have hq := RingHom.congr_fun (divisorMap_comp_scalarMap (algebraMap k L) p.val
        (β i).val.val (β i).property) a
      simp only [RingHom.comp_apply] at hq ⊢
      rw [← hq]
      exact h
    have hnorm := finiteExtensionNorm_map_algEquiv η n
      (map n (adjoinRootMap (algebraMap k L) p.val (β i).val.val (β i).property) x)
    rw [← hnorm, ← hmap, map_comp, LinearMap.comp_apply]

open scoped TensorProduct in
/-- Any actual scalar tensor decomposition computes the restricted finite norm
by its full field-coordinate sum, on the original field and all classes. -/
theorem finiteExtensionNorm_restrict_tensorProduct
    (E : Type*) [Field E] [Algebra k E] [FiniteDimensional k E]
    (e : L ⊗[k] E ≃ₐ[L] ∀ i, D i) (n : ℕ) (x : K E n) :
    map n (algebraMap k L) (finiteExtensionNorm k E n x) =
      ∑ i, finiteExtensionNorm L (D i) n
        (map n (((Pi.evalRingHom D i).comp e.toRingHom).comp
          Algebra.TensorProduct.includeRight.toRingHom) x) := by
  let p := finiteNormPolynomial k E
  let ε := finiteNormPresentation k E
  let e' := (scalarExtensionEquiv (L := L) p.val).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) ε).trans e)
  rw [finiteExtensionNorm_eq_presentation k E n p ε, LinearMap.comp_apply,
    polynomialNorm_restrict_fieldProduct D p e']
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_apply
    (map n (((Pi.evalRingHom D i).comp e'.toRingHom).comp (scalarMap (algebraMap k L) p.val)))
    (map n ε.symm.toRingHom), ← map_comp]
  congr 2
  congr 1
  apply RingHom.ext
  intro a
  have hs := RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (L := L) p.val)
    (ε.symm a)
  change scalarExtensionEquiv p.val (1 ⊗ₜ[k] ε.symm a) =
    scalarMap (algebraMap k L) p.val (ε.symm a) at hs
  change e' (scalarMap (algebraMap k L) p.val (ε.symm a)) i = e (1 ⊗ₜ[k] a) i
  rw [← hs]
  simp only [e', AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change e (1 ⊗ₜ[k] ε (ε.symm a)) i = _
  rw [AlgEquiv.apply_symm_apply]

end MilnorK
