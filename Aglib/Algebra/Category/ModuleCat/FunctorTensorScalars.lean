/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensorFiniteness
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Original commuting scalars on the canonical tensor comparison

The native tensor module action is on its left factor. Transporting that action
across the native tensor commutor gives the right-factor action without changing
the tensor carrier or additive structure. The canonical comparison is linear
for this action whenever its actual coefficient scalar maps give the target
action. Its inverse is then linear as well.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

universe r v w i l

namespace TensorProduct

variable (R : Type r) [CommRing R] (Λ : Type l) [Ring Λ]
  (V : Type w) [AddCommGroup V] [Module R V]
  (M : Type v) [AddCommGroup M] [Module R M] [Module Λ M] [SMulCommClass Λ R M]

/-- The commuting action on the right factor, transported through the native commutor. -/
@[instance_reducible]
def rightModule : Module Λ (V ⊗[R] M) := by
  let := SMulCommClass.symm Λ R M
  exact (TensorProduct.comm R V M).toAddEquiv.module Λ

/-- The transferred action is exactly scalar multiplication on the right factor. -/
theorem rightModule_smul_tmul (a : Λ) (x : V) (m : M) :
    letI := rightModule R Λ V M
    a • (x ⊗ₜ[R] m) = x ⊗ₜ[R] (a • m) := by
  let := SMulCommClass.symm Λ R M
  let := rightModule R Λ V M
  change (TensorProduct.comm R M V)
    (a • (TensorProduct.comm R V M) (x ⊗ₜ[R] m)) = _
  rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_tmul]

end TensorProduct

namespace ModuleCat

variable {R : Type r} [CommRing R]
  (F : ModuleCat.{max r v} R ⥤ ModuleCat.{w} R) [F.Additive] [F.Linear R]
  {M : ModuleCat.{max r v} R}
  (Λ : Type l) [Ring Λ] [Module Λ M] [SMulCommClass Λ R M]
  [Module Λ (F.obj M)]
  (hscalar : ∀ (a : Λ) (x : F.obj M),
    F.map (ModuleCat.ofHom (DistribSMul.toLinearMap R M a)) x = a • x)

/-- The unchanged canonical tensor comparison, linear for the original commuting scalars. -/
def functorTensorComparisonOver :
    letI := TensorProduct.rightModule R Λ (F.obj (liftedUnit.{r, v} R)) M
    F.obj (liftedUnit.{r, v} R) ⊗[R] M →ₗ[Λ] F.obj M := by
  letI := TensorProduct.rightModule R Λ (F.obj (liftedUnit.{r, v} R)) M
  refine
    { (functorTensorComparison F M).toAddMonoidHom with
      map_smul' := ?_ }
  intro a z
  change functorTensorComparison F M (a • z) = a • functorTensorComparison F M z
  induction z using TensorProduct.inductionOn with
  | tmul x m =>
      rw [TensorProduct.rightModule_smul_tmul]
      exact (functorTensorPairingOver F Λ hscalar x).map_smul a m
  | add z t hz ht =>
      simp only [smul_add, map_add, hz, ht]

/-- Scalar enrichment does not alter the comparison function. -/
@[simp]
theorem functorTensorComparisonOver_apply
    (z : F.obj (liftedUnit.{r, v} R) ⊗[R] M) :
    functorTensorComparisonOver F Λ hscalar z = functorTensorComparison F M z := rfl

/-- The canonical equivalence and its inverse respect the original commuting scalars. -/
def functorTensorEquivOverOfBasis {ι : Type i} (b : Basis ι R M)
    [PreservesColimitsOfShape (Discrete ι) F] :
    letI := TensorProduct.rightModule R Λ (F.obj (liftedUnit.{r, v} R)) M
    F.obj (liftedUnit.{r, v} R) ⊗[R] M ≃ₗ[Λ] F.obj M := by
  letI := TensorProduct.rightModule R Λ (F.obj (liftedUnit.{r, v} R)) M
  exact LinearEquiv.ofBijective (functorTensorComparisonOver F Λ hscalar)
    ⟨functorTensorComparison_injective_of_basis F b,
      functorTensorComparison_surjective_of_basis F b⟩

end ModuleCat
