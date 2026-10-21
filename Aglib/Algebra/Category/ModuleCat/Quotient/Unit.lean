/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # The original scalar-extension unit for a surjective ring map -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]

/-- Scalar extension along a surjective ring map is a quotient, on the
original adjunction unit and without finiteness assumptions. -/
theorem extendRestrictScalarsAdj_unit_surjective (φ : R →+* S)
    (hφ : Function.Surjective φ) (M : ModuleCat.{max v w} R) :
    Function.Surjective ((extendRestrictScalarsAdj φ).unit.app M) := by
  let : Module R S := Module.compHom S φ
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hφ s
    refine ⟨r • m, ?_⟩
    change (1 : S) ⊗ₜ[R,φ] (r • m) = φ r ⊗ₜ[R,φ] m
    rw [TensorProduct.tmul_smul]
    change (φ r * 1) ⊗ₜ[R,φ] m = φ r ⊗ₜ[R,φ] m
    rw [mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- Categorical form of surjectivity of the original scalar-extension unit. -/
theorem extendRestrictScalarsAdj_unit_epi (φ : R →+* S)
    (hφ : Function.Surjective φ) (M : ModuleCat.{max v w} R) :
    Epi ((extendRestrictScalarsAdj φ).unit.app M) :=
  (epi_iff_surjective _).mpr (extendRestrictScalarsAdj_unit_surjective φ hφ M)

end ModuleCat
