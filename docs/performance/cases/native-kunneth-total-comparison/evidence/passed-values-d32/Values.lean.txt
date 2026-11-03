/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethComparison

/-!
# Original values of the total Kunneth operator

The whole comparison with the original signed external product is established
before evaluation. Its homogeneous values are the original external cup.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace LinearMap

/-- Evaluate the original whole comparison and component map over their given modules. -/
private theorem tmul_eq_of_whole_component
    {R A B C S M N P : Type*} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [AddCommMonoid C] [Module R C] [AddCommMonoid S] [Module R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    {Φ : S →ₗ[R] C} {s : A ⊗[R] B →ₗ[R] S} {L : A ⊗[R] B →ₗ[R] C}
    {I_M : M →ₗ[R] A} {I_N : N →ₗ[R] B} {I_P : P →ₗ[R] C}
    {T : M ⊗[R] N →ₗ[R] P} {e : M → N → P}
    (hWhole : Φ ∘ₗ s = L)
    (hComponent : Φ ∘ₗ s ∘ₗ TensorProduct.map I_M I_N = I_P ∘ₗ T)
    (hT : ∀ x y, T (x ⊗ₜ[R] y) = e x y) (x : M) (y : N) :
    L (I_M x ⊗ₜ[R] I_N y) = I_P (e x y) := by
  have hL := LinearMap.congr_fun hWhole (I_M x ⊗ₜ[R] I_N y)
  have hF := LinearMap.congr_fun hComponent (x ⊗ₜ[R] y)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at hL hF
  exact hL.symm.trans (hF.trans (congrArg I_P (hT x y)))

end LinearMap

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

set_option maxHeartbeats 1000000 in
-- Kernel checking of this original homogeneous value law exceeds the standard
-- 200000-heartbeat limit. Keep the finite allowance local to this proof.
/-- The original total operator has the original homogeneous external-cup value. -/
theorem structureExternalLinearMap_tmul {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalLinearMap X Y
        (structureCohomologyInclusion X p x ⊗ₜ[k] structureCohomologyInclusion Y q y) =
      structureCohomologyInclusion (X ⊗ Y) n (structureExternalCup X Y h x y) := by
  have hValue := LinearMap.tmul_eq_of_whole_component
    (structureExternalLinearMap_signed X Y)
    (structureExternalAlgebraMap_tensor X Y h)
    (structureExternalTensor_tmul X Y h) x y
  exact hValue

end AlgebraicGeometry.Scheme.Cohomology
