/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Right-factor tensor actions and finite residue syzygies

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 1500–1650.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Module.Flat.ResidueSyzygies
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (C : Type*) [AddCommGroup C] [Module R C]

/-- The right-factor S-action on C ⊗[R] M, transported through tensor commutativity.
This is deliberately not a global instance, avoiding the two-action diamond. -/
@[instance_reducible]
def tensorRightModule : Module S (C ⊗[R] M) :=
  (TensorProduct.comm R C M).toAddEquiv.module S

attribute [local instance 50] tensorRightModule

@[simp] theorem right_smul_tmul (s : S) (c : C) (m : M) :
    s • (c ⊗ₜ[R] m) = c ⊗ₜ[R] (s • m) := rfl

local instance tensorRight_isScalarTower : IsScalarTower R S (C ⊗[R] M) where
  smul_assoc r s x := by
    induction x with
    | tmul c m =>
      simp only [right_smul_tmul, smul_tmul', smul_assoc]
      exact (smul_tmul r c (s • m)).symm
    | add x y hx hy => simp_all [smul_add]

/-- Scalar extension remains S-linear for the transported right-factor actions. -/
def baseChangeLinearMap (f : M →ₗ[S] N) : (C ⊗[R] M) →ₗ[S] (C ⊗[R] N) where
  toFun := (f.restrictScalars R).lTensor C
  map_add' := map_add _
  map_smul' s x := by
    induction x with
    | tmul c m =>
      change c ⊗ₜ[R] (f (s • m)) = c ⊗ₜ[R] (s • f m)
      rw [f.map_smul]
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem baseChangeLinearMap_apply (f : M →ₗ[S] N) (x : C ⊗[R] M) :
    baseChangeLinearMap C f x = (f.restrictScalars R).lTensor C x := rfl

@[simp] theorem baseChangeLinearMap_tmul (f : M →ₗ[S] N) (c : C) (m : M) :
    baseChangeLinearMap C f (c ⊗ₜ[R] m) = c ⊗ₜ[R] f m := rfl

end Module.Flat.ResidueSyzygies

namespace Module.Flat.ResidueSyzygies
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (C : Type*) [CommRing C] [Algebra R C]
attribute [local instance 50] tensorRightModule

/-- A cyclic scalar extension of an S-finite module remains S-finite. -/
theorem finite_of_surjective [Module.Finite S M]
    (hC : Function.Surjective (algebraMap R C)) : Module.Finite S (C ⊗[R] M) := by
  let j : M →ₗ[S] C ⊗[R] M :=
    { toFun := fun m ↦ (1 : C) ⊗ₜ[R] m
      map_add' := by intro x y; exact tmul_add _ _ _
      map_smul' := by intro s m; rfl }
  have hj : Function.Surjective j := by
    intro x
    obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective M
      (show Function.Surjective (Algebra.linearMap R C) from hC) x
    obtain ⟨m, rfl⟩ := (TensorProduct.lid R M).symm.surjective y
    refine ⟨m, ?_⟩
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      Algebra.linearMap_apply, map_one]
    rfl
  exact Module.Finite.of_surjective j hj

/-- Actual fibre syzygies admit finitely many generators over the Noetherian
acting algebra. This uses no flatness of the fibre quotient. -/
theorem exists_finite_kernel_generators [IsNoetherianRing S] [Module.Finite S M]
    (hC : Function.Surjective (algebraMap R C)) (f : M →ₗ[S] N) :
    ∃ (n : ℕ) (x : Fin n → C ⊗[R] M),
      (∀ i, (f.restrictScalars R).lTensor C (x i) = 0) ∧
      Submodule.span S (Set.range x) = (baseChangeLinearMap (R := R) C f).ker := by
  have : Module.Finite S (C ⊗[R] M) := finite_of_surjective C hC
  have hfg : (baseChangeLinearMap (R := R) C f).ker.FG := IsNoetherian.noetherian _
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨n, x, ?_, hx⟩
  intro i
  change x i ∈ (baseChangeLinearMap (R := R) C f).ker
  rw [← hx]
  exact Submodule.subset_span (Set.mem_range_self i)

end Module.Flat.ResidueSyzygies

namespace Module.Flat.ResidueSyzygies
universe wC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
attribute [local instance 50] tensorRightModule
attribute [local instance] tensorRight_isScalarTower

/-- The scalar-extension unit is linear for the right S-action. -/
def scalarToTensor (K : Type*) [CommRing K] [Algebra R K] : M →ₗ[S] K ⊗[R] M where
  toFun := fun m ↦ (1 : K) ⊗ₜ[R] m
  map_add' := by intro x y; exact tmul_add _ _ _
  map_smul' := by intro s m; rfl

/-- Old residue vectors which admit genuine relation lifts at a fixed stage
form a submodule over the original acting algebra. -/
def liftableRelations (K C : Type*) [CommRing K] [Algebra R K]
    [CommRing C] [Algebra R C] (f : M →ₗ[S] N) : Submodule S (K ⊗[R] M) where
  carrier := {x | ∃ u : C ⊗[R] M,
    (f.restrictScalars R).baseChange C u = 0 ∧
    (TensorProduct.mk R K M 1).baseChange C u = (1 : C) ⊗ₜ[R] x}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu, hqu⟩ ⟨v, hv, hqv⟩
    exact ⟨u + v, by simp [hu, hv], by simp [hqu, hqv, tmul_add]⟩
  smul_mem' := by
    rintro s x ⟨u, hu, hqu⟩
    refine ⟨s • u, ?_, ?_⟩
    · change baseChangeLinearMap (R := R) C f (s • u) = 0
      rw [map_smul]
      change s • ((f.restrictScalars R).baseChange C u) = 0
      rw [hu, smul_zero]
    · change baseChangeLinearMap (R := R) C (scalarToTensor (R := R) (S := S) K)
        (s • u) = (1 : C) ⊗ₜ[R] (s • x)
      rw [map_smul]
      change s • ((TensorProduct.mk R K M 1).baseChange C u) = _
      rw [hqu, right_smul_tmul]

/-- Finitely many genuine old residue syzygies suffice to establish the
universal lifting hypothesis, at any later scalar stage. -/
theorem exists_finite_syzygies_suffice
    (K : Type*) [CommRing K] [Algebra R K] [IsNoetherianRing S] [Module.Finite S M]
    (hK : Function.Surjective (algebraMap R K)) (f : M →ₗ[S] N) :
    ∃ (n : ℕ) (x : Fin n → K ⊗[R] M),
      (∀ i, (f.restrictScalars R).lTensor K (x i) = 0) ∧
      ∀ (C : Type wC) [CommRing C] [Algebra R C],
        (∀ i, ∃ u : C ⊗[R] M,
          (f.restrictScalars R).baseChange C u = 0 ∧
          (TensorProduct.mk R K M 1).baseChange C u = (1 : C) ⊗ₜ[R] x i) →
        ∀ y : K ⊗[R] M, (f.restrictScalars R).lTensor K y = 0 →
          ∃ u : C ⊗[R] M,
            (f.restrictScalars R).baseChange C u = 0 ∧
            (TensorProduct.mk R K M 1).baseChange C u = (1 : C) ⊗ₜ[R] y := by
  obtain ⟨n, x, hx, hspan⟩ := exists_finite_kernel_generators K hK f
  refine ⟨n, x, hx, ?_⟩
  intro C _ _ hlift y hy
  have hle : (baseChangeLinearMap (R := R) K f).ker ≤ liftableRelations K C f := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hlift i
  exact hle hy

end Module.Flat.ResidueSyzygies
