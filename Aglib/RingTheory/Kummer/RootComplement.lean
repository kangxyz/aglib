/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # The original map between the parameter and root complements

The native localization lift maps the parameter complement directly into the
root complement. No second localization at the power of the root is chosen.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

variable {R : Type*} [CommRing R] (N : ℕ) (f : R)

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)

/-- The literal root map on the complements, implemented by the native
localization universal property and the original root-power equation. -/
def rootComplementHom : Localization.Away f →+* Localization.Away θ :=
  IsLocalization.Away.lift f (g := algebraMap R (Localization.Away θ)) (by
    rw [IsScalarTower.algebraMap_apply R T (Localization.Away θ), ← root_pow,
      map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit θ).pow N)

@[simp]
theorem rootComplementHom_algebraMap (r : R) :
    rootComplementHom N f (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away θ) r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The complement map retains the unchanged coefficient triangle. -/
theorem rootComplementHom_comp :
    (rootComplementHom N f).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.Away θ) :=
  IsLocalization.Away.lift_comp _ _

/-- For a nonzero parameter and a domain root algebra, the original complement
map is injective. Positivity supplies the faithful monic root basis. -/
theorem rootComplementHom_injective [IsDomain R] [IsDomain T]
    (hN : 0 < N) (hf : f ≠ 0) : Function.Injective (rootComplementHom N f) := by
  let : Module.Free R T :=
    (Polynomial.monic_X_pow_sub_C f (Nat.ne_of_gt hN)).free_adjoinRoot
  have hR : Function.Injective (algebraMap R T) := FaithfulSMul.algebraMap_injective R T
  have hθ : θ ≠ 0 := by
    intro hz
    apply hf
    apply hR
    rw [map_zero, ← root_pow N f, hz, zero_pow (Nat.ne_of_gt hN)]
  have hi : Function.Injective (algebraMap T (Localization.Away θ)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hθ)
  have hj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)
    (rootComplementHom N f)).mpr
  intro a b
  simp only [rootComplementHom_algebraMap, IsScalarTower.algebraMap_apply R T
    (Localization.Away θ), hi.eq_iff, hR.eq_iff, hj.eq_iff]

end Algebra.Kummer
