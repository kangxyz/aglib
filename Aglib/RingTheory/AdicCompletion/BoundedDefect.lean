/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bounded defects under reduction by a second ideal

If an ideal kills both defects of a linear map, its square kills the kernel
of every ideal reduction. The original ideal still kills the cokernel.
These bounds do not require flatness, finiteness, or completeness. They are
the algebraic bounds used in the two-ideal reconstruction argument.
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Killing the original kernel controls inverse images of images, uniformly
in the chosen submodule. -/
theorem smul_comap_map_le (f : M →ₗ[R] N) (J : Ideal R)
    (hker : J • f.ker = ⊥) (P : Submodule R M) :
    J • (P.map f).comap f ≤ P := by
  rw [Submodule.comap_map_eq, Submodule.smul_sup, hker, sup_bot_eq]
  exact Submodule.smul_le_right

/-- If `J` kills both defects of `f`, its square sends the preimage of
`K N` into `K M`, for every second ideal `K`. -/
theorem sq_smul_comap_ideal_le (f : M →ₗ[R] N) (J K : Ideal R)
    (hker : J • f.ker = ⊥) (hcoker : J • (⊤ : Submodule R N) ≤ f.range) :
    J ^ 2 • (K • (⊤ : Submodule R N)).comap f ≤ K • (⊤ : Submodule R M) := by
  have hJK : J • (K • (⊤ : Submodule R N)) ≤
      (K • (⊤ : Submodule R M)).map f := by
    rw [← Submodule.mul_smul, mul_comm J K, Submodule.mul_smul,
      Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl hcoker
  calc
    J ^ 2 • (K • (⊤ : Submodule R N)).comap f =
        J • (J • (K • (⊤ : Submodule R N)).comap f) := by
      rw [pow_two, Submodule.mul_smul]
    _ ≤ J • (J • (K • (⊤ : Submodule R N))).comap f :=
      Submodule.smul_mono le_rfl (Submodule.smul_comap_le_comap_smul _ _ _)
    _ ≤ J • ((K • (⊤ : Submodule R M)).map f).comap f :=
      Submodule.smul_mono le_rfl (Submodule.comap_mono hJK)
    _ ≤ K • (⊤ : Submodule R M) := f.smul_comap_map_le J hker _

/-- The square bound holds for the actual induced quotient map, not merely
for an abstract isomorphic cokernel presentation. -/
theorem sq_smul_ker_mapQ_eq_bot (f : M →ₗ[R] N) (J K : Ideal R)
    (hker : J • f.ker = ⊥) (hcoker : J • (⊤ : Submodule R N) ≤ f.range) :
    J ^ 2 • (Submodule.mapQ (K • (⊤ : Submodule R M))
      (K • (⊤ : Submodule R N)) f
      (Submodule.smul_top_le_comap_smul_top K f)).ker = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hm : m ∈ (K • (⊤ : Submodule R N)).comap f := by
    change Submodule.Quotient.mk (f m) = 0 at hx
    change f m ∈ K • (⊤ : Submodule R N)
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  have ham : a • m ∈ K • (⊤ : Submodule R M) :=
    f.sq_smul_comap_ideal_le J K hker hcoker (Submodule.smul_mem_smul ha hm)
  change Submodule.Quotient.mk (a • m) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ham

/-- The cokernel bound does not increase when reducing by another ideal. -/
theorem smul_top_le_range_mapQ (f : M →ₗ[R] N) (J K : Ideal R)
    (hcoker : J • (⊤ : Submodule R N) ≤ f.range) :
    J • (⊤ : Submodule R (N ⧸ (K • (⊤ : Submodule R N)))) ≤
      (Submodule.mapQ (K • (⊤ : Submodule R M))
        (K • (⊤ : Submodule R N)) f
        (Submodule.smul_top_le_comap_smul_top K f)).range := by
  apply Submodule.smul_le.mpr
  intro a ha y _
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := hcoker (Submodule.smul_mem_smul ha
    (Submodule.mem_top : n ∈ (⊤ : Submodule R N)))
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  change Submodule.Quotient.mk (f m) = Submodule.Quotient.mk (a • n)
  rw [hm]

end LinearMap
