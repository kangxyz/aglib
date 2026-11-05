/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalars
public import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Finite-type right tensor values

A finite original left carrier gives a surjection from a finite sum of copies
of the original right module. This does not require a map between the two
coefficient rings, a scalar-extension model, or a choice of vector-space basis.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ModuleCat

universe r l v w

variable (R : Type r) [CommRing R] (Λ : Type l) [Ring Λ]
  (M : Type v) [AddCommGroup M] [Module R M] [Module Λ M] [SMulCommClass Λ R M]
  (V : ModuleCat.{w} R)

/-- The right-factor coefficient action on the tensor in the finite presentation. -/
local instance tensorRightScalarsFiniteModule : Module Λ (V ⊗[R] M) :=
  TensorProduct.rightModule R Λ V M

/-- The original pure-tensor map is linear for the right coefficient action. -/
def tensorRightScalarsPure (x : V) : M →ₗ[Λ] V ⊗[R] M where
  toFun m := x ⊗ₜ[R] m
  map_add' m n := TensorProduct.tmul_add x m n
  map_smul' a m := (TensorProduct.rightModule_smul_tmul R Λ V M a x m).symm

/-- Sum of the original pure-tensor maps, with the original tensor as target. -/
def tensorRightScalarsPresentation : (V →₀ M) →ₗ[Λ] V ⊗[R] M :=
  Finsupp.lsum ℕ (tensorRightScalarsPure R Λ M V)

/-- Every original tensor is in the image of the same presentation. -/
theorem tensorRightScalarsPresentation_surjective :
    Function.Surjective (tensorRightScalarsPresentation R Λ M V) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x m =>
      exact ⟨Finsupp.single x m,
        Finsupp.lsum_single ℕ (tensorRightScalarsPure R Λ M V) x m⟩
  | add z t hz ht =>
      obtain ⟨a, rfl⟩ := hz
      obtain ⟨b, rfl⟩ := ht
      exact ⟨a + b, (tensorRightScalarsPresentation R Λ M V).map_add a b⟩

/-- A finite left carrier and finite-type right module give finite-type values
for the actual right-factor tensor action. -/
theorem tensorRightScalars_finite [Finite V] [Module.Finite Λ M] :
    Module.Finite Λ (V ⊗[R] M) :=
  Module.Finite.of_surjective (tensorRightScalarsPresentation R Λ M V)
    (tensorRightScalarsPresentation_surjective R Λ M V)

end ModuleCat
