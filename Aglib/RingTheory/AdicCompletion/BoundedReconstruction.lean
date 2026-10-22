/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedReconstructionFinite
public import Aglib.RingTheory.AdicCompletion.BoundedCokernel
public import Aglib.RingTheory.AdicCompletion.CompletedLift
public import Aglib.RingTheory.AdicCompletion.ExactReconstruction
public import Aglib.RingTheory.AdicCompletion.FiniteModule

/-!
# Same-ideal bounded affine reconstruction

The original fibre product is finite over the original ring, and its canonical
completed-linear first projection is an equivalence. The completion ideal is
also the ideal bounding the defects. The original ring need not be complete.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u
variable {R M N : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [AddCommGroup M] [Module R M]
  [Module (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) M]
  [Module.Finite (AdicCompletion I R) M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- A finite module over a Noetherian completion is complete for the original
ideal after restriction of scalars. -/
theorem isAdicComplete_of_finite_completed : IsAdicComplete I M := by
  let : IsNoetherianRing (AdicCompletion I R) := AdicCompletion.isNoetherianRing R I
  let : IsAdicComplete I (AdicCompletion I R) := isAdicComplete I.fg_of_isNoetherianRing
  let : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R)))
      (AdicCompletion I R) := (IsAdicComplete.map_algebraMap_iff I _).mpr inferInstance
  exact (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion I R) I M).mp
    (IsAdicComplete.of_finite (AdicCompletion I R)
      (I.map (algebraMap R (AdicCompletion I R))) M)

/-- The actual completed first projection of the native bounded pullback is
bijective. Only its kernel, not all of the completed source, descends to a
finite module over the original ring. -/
theorem bounded_pullback_completion_bijective
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N) (t : ℕ)
    (hker : I ^ t • (f.restrictScalars R).ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R (AdicCompletion I N)) ≤
      (f.restrictScalars R).range) :
    let := finite_pullback_of_pow_ker_eq_bot I f t hker
    Function.Bijective (liftFiniteLinearMap I
      (LinearMap.pullbackKernelFst (f.restrictScalars R) (of I N))) := by
  let fR := f.restrictScalars R
  let P := LinearMap.pullbackKernel fR (of I N)
  let K := fR.ker
  let C := AdicCompletion I N ⧸ fR.range
  let p : P →ₗ[R] N := LinearMap.pullbackKernelSnd fR (of I N)
  let a : P →ₗ[R] M := LinearMap.pullbackKernelFst fR (of I N)
  let i : K →ₗ[R] P := LinearMap.kerToPullbackKernel fR (of I N)
  let c : AdicCompletion I N →ₗ[R] C := fR.range.mkQ
  let : Module.Finite R P := finite_pullback_of_pow_ker_eq_bot I f t hker
  have hC : I ^ t • (⊤ : Submodule R C) = ⊥ :=
    LinearMap.smul_top_quotient_range_eq_bot fR (I ^ t) hcoker
  have hq : Function.Surjective (c.comp (of I N)) :=
    surjective_comp_of_of_pow_smul_eq_bot I I.fg_of_isNoetherianRing t c
      fR.range.mkQ_surjective hC
  let : Module.Finite R C := Module.Finite.of_surjective _ hq
  have hK : I ^ t • (⊤ : Submodule R K) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro r hr x _
    have hz := Submodule.smul_mem_smul hr (show x.val ∈ fR.ker from x.property)
    rw [hker] at hz
    change r • x = 0
    apply Subtype.ext
    exact hz
  let : IsAdicComplete I K := IsAdicComplete.of_pow_smul_eq_bot I t hK
  let : IsAdicComplete I M := isAdicComplete_of_finite_completed I
  have hbi : Function.Bijective ((ofLinearEquiv I M).symm.toLinearMap.comp
      ((map I a).restrictScalars R)) := by
    apply completion_bijective_of_exact I i p fR.ker.subtype fR c a
    · exact LinearMap.kerToPullbackKernel_exact fR (of I N)
    · exact LinearMap.pullbackKernelSnd_exact_cokernel fR (of I N)
    · exact Subtype.val_injective
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact x.property
    · intro y
      exact Submodule.Quotient.mk_eq_zero _
    · rfl
    · exact LinearMap.pullbackKernel_comm fR (of I N)
  change Function.Bijective (liftFiniteLinearMap I a)
  change Function.Bijective ((liftFiniteLinearMap I a).restrictScalars R)
  rw [liftFiniteLinearMap_restrictScalars]
  exact hbi

/-- The canonical completed-linear reconstruction equivalence. -/
def boundedPullbackCompletionEquiv
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N) (t : ℕ)
    (hker : I ^ t • (f.restrictScalars R).ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R (AdicCompletion I N)) ≤
      (f.restrictScalars R).range) :
    AdicCompletion I (LinearMap.pullbackKernel (f.restrictScalars R) (of I N)) ≃ₗ[
      AdicCompletion I R] M := by
  let := finite_pullback_of_pow_ker_eq_bot I f t hker
  exact LinearEquiv.ofBijective
    (liftFiniteLinearMap I (LinearMap.pullbackKernelFst (f.restrictScalars R) (of I N)))
    (bounded_pullback_completion_bijective I f t hker hcoker)

@[simp]
theorem boundedPullbackCompletionEquiv_of
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N) (t : ℕ)
    (hker : I ^ t • (f.restrictScalars R).ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R (AdicCompletion I N)) ≤
      (f.restrictScalars R).range)
    (x : LinearMap.pullbackKernel (f.restrictScalars R) (of I N)) :
    boundedPullbackCompletionEquiv I f t hker hcoker (of I _ x) = x.val.1 := by
  let := finite_pullback_of_pow_ker_eq_bot I f t hker
  exact liftFiniteLinearMap_of I _ x

/-- The comparison preserves the ORIGINAL map to the completed target. -/
theorem boundedPullbackCompletionEquiv_comp
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N) (t : ℕ)
    (hker : I ^ t • (f.restrictScalars R).ker = ⊥)
    (hcoker : I ^ t • (⊤ : Submodule R (AdicCompletion I N)) ≤
      (f.restrictScalars R).range) :
    f.comp (boundedPullbackCompletionEquiv I f t hker hcoker).toLinearMap =
      map I (LinearMap.pullbackKernelSnd (f.restrictScalars R) (of I N)) := by
  apply LinearMap.restrictScalars_injective R
  apply linearMap_ext_of I I.fg_of_isNoetherianRing
  intro x
  change f (boundedPullbackCompletionEquiv I f t hker hcoker (of I _ x)) =
    map I (LinearMap.pullbackKernelSnd (f.restrictScalars R) (of I N)) (of I _ x)
  rw [boundedPullbackCompletionEquiv_of, map_of]
  exact LinearMap.congr_fun (LinearMap.pullbackKernel_comm (f.restrictScalars R) (of I N)) x

end AdicCompletion
