/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Tensor
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Adic thickening and separatedness criteria for injectivity over a local base

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 91–94, 292–378, 393–406.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Module.Flat
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The canonical inclusion of the `n`-th `I`-adic layer into `R ⧸ I ^ (n + 1)`. -/
def powLayerMap (I : Ideal R) (n : ℕ) :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) →ₗ[R]
      R ⧸ I ^ (n + 1) :=
  Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) (by
    intro x hx
    simpa [Submodule.mem_smul_top_iff, pow_succ'] using hx)

@[simp] theorem powLayerMap_mk (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    powLayerMap I n (Submodule.Quotient.mk x) = Ideal.Quotient.mk (I ^ (n + 1)) x := rfl

theorem powLayerMap_injective (I : Ideal R) (n : ℕ) :
    Function.Injective (powLayerMap I n) := by
  intro a b h
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  simpa [Submodule.Quotient.eq, Ideal.Quotient.eq, Submodule.mem_smul_top_iff,
    pow_succ'] using h

theorem powLayerMap_exact (I : Ideal R) (n : ℕ) :
    Function.Exact (powLayerMap I n)
      (Submodule.factor (Ideal.pow_le_pow_right n.le_succ)) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    have hx' : x ∈ I ^ n := Ideal.Quotient.eq_zero_iff_mem.mp hx
    exact ⟨Submodule.Quotient.mk ⟨x, hx'⟩, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨y, hy'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← hy]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy'

/-- Over a residue field, injectivity lifts to every ideal-adic thickening
when the target module is flat over the original ring. -/
theorem lTensor_quotient_pow_injective [Module.Flat R N]
    (I : Ideal R) [I.IsMaximal] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (R ⧸ I))) (n : ℕ) :
    Function.Injective (f.lTensor (R ⧸ I ^ n)) := by
  induction n with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      intro x y _
      exact Subsingleton.elim _ _
  | succ n ih =>
      let := Ideal.Quotient.field I
      let Q := ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)))
      have hQ : Function.Injective (f.lTensor Q) :=
        lTensor_injective_of_baseChange_injective (R ⧸ I) Q f hf
      exact lTensor_injective_of_exact f (powLayerMap I n)
        (Submodule.factor (Ideal.pow_le_pow_right n.le_succ)) (powLayerMap_injective I n)
        (Submodule.factor_surjective _) (powLayerMap_exact I n) hQ ih

/-- Adic separation turns fibrewise injectivity into injectivity of the map.
No Noetherian hypothesis is needed once separation is known. -/
theorem injective_of_residue_injective_of_isHausdorff [Module.Flat R N]
    (I : Ideal R) [I.IsMaximal] [IsHausdorff I M]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor (R ⧸ I))) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hx0 : f x = 0 := hx
  apply IsHausdorff.haus' (I := I)
  intro n
  have ht : (1 : R ⧸ I ^ n) ⊗ₜ[R] x = 0 :=
    lTensor_quotient_pow_injective I f hf n (by simp [hx0])
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul M (I ^ n)) ht
  simpa [SModEq.zero, Submodule.Quotient.mk_eq_zero] using hq

/-- The injectivity conclusion of Stacks 00ME. The base local ring may be
non-Noetherian; only the local ring acting finitely on the source is Noetherian. -/
theorem injective_of_residue_injective_of_noetherian
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S M] [IsScalarTower R S M] [Module.Finite S M] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R))) :
    Function.Injective f := by
  have : IsHausdorff (IsLocalRing.maximalIdeal S) M :=
    ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
      (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal_le_jacobson _)).le
        (by simpa [SModEq.zero] using hx)⟩
  have : IsHausdorff (IsLocalRing.maximalIdeal R) M :=
    IsHausdorff.of_map (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  exact injective_of_residue_injective_of_isHausdorff (IsLocalRing.maximalIdeal R) f hf

/-- Variant of the local injectivity criterion using any surjective residue-field map. -/
theorem injective_of_field_fibre_injective_of_noetherian
    (S K : Type*) [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S M] [IsScalarTower R S M] [Module.Finite S M] [Module.Flat R N]
    (hK : Function.Surjective (algebraMap R K)) (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor K)) : Function.Injective f := by
  let p := RingHom.ker (algebraMap R K)
  have hp : p.IsMaximal := RingHom.ker_isMaximal_of_surjective (algebraMap R K) hK
  let e : (R ⧸ p) ≃ₐ[R] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R K) hK
  have hf' := lTensor_injective_of_linearEquiv e.toLinearEquiv f hf
  have heq : p = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hp
  rw [heq] at hf'
  exact injective_of_residue_injective_of_noetherian S f hf'

end Module.Flat
