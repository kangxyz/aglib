/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedCompletionSquare
public import Aglib.RingTheory.AdicCompletion.PullbackFunctoriality

/-!
# Uniqueness of bounded reconstruction triples

Candidates retain an original finite map with bounded kernel and cokernel.
An isomorphism of completions alone is not a uniqueness hypothesis.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u
variable {R F M N : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [AddCommGroup F] [Module R F] [Module.Finite R F]
  [AddCommGroup M] [Module R M] [Module (AdicCompletion I R) M]
  [IsScalarTower R (AdicCompletion I R) M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- A bounded reconstruction triple is canonically the original fibre product,
using its specified completion isomorphism and its original map to the target. -/
def candidatePullbackEquiv
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range)
    (β : AdicCompletion I F ≃ₗ[AdicCompletion I R] M)
    (hβ : f.comp β.toLinearMap = map I a) :
    F ≃ₗ[R] LinearMap.pullbackKernel (f.restrictScalars R) (of I N) :=
  (completionPullbackEquiv I a t hker hcoker).trans
    (LinearMap.pullbackKernelCongrFst ((map I a).restrictScalars R)
      (f.restrictScalars R) (of I N) (β.restrictScalars R)
      (congrArg (fun q => q.restrictScalars R) hβ))

@[simp]
theorem candidatePullbackEquiv_fst
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range)
    (β : AdicCompletion I F ≃ₗ[AdicCompletion I R] M)
    (hβ : f.comp β.toLinearMap = map I a) (x : F) :
    (candidatePullbackEquiv I f a t hker hcoker β hβ x).val.1 = β (of I F x) := rfl

@[simp]
theorem candidatePullbackEquiv_snd
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range)
    (β : AdicCompletion I F ≃ₗ[AdicCompletion I R] M)
    (hβ : f.comp β.toLinearMap = map I a) (x : F) :
    (candidatePullbackEquiv I f a t hker hcoker β hβ x).val.2 = a x := rfl

/-- Uniqueness is relative to BOTH original projections, including the chosen
formal comparison. It applies in particular to compatible isomorphisms. -/
theorem candidatePullbackEquiv_unique
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (a : F →ₗ[R] N) (t : ℕ)
    (hker : I ^ t • a.ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R N) ≤ a.range)
    (β : AdicCompletion I F ≃ₗ[AdicCompletion I R] M)
    (hβ : f.comp β.toLinearMap = map I a)
    (d : F →ₗ[R] LinearMap.pullbackKernel (f.restrictScalars R) (of I N))
    (hd₁ : ∀ x, (d x).val.1 = β (of I F x))
    (hd₂ : ∀ x, (d x).val.2 = a x) :
    d = (candidatePullbackEquiv I f a t hker hcoker β hβ).toLinearMap := by
  apply LinearMap.pullbackKernel_hom_ext (f.restrictScalars R) (of I N)
  · apply LinearMap.ext
    intro x
    exact hd₁ x
  · apply LinearMap.ext
    intro x
    exact hd₂ x

end AdicCompletion
