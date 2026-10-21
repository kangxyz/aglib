/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTowerMultiplication
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Boundary
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# The actual direct sum of ideal-power cohomology

The total object is the native direct sum of the original `Sheaf.H` modules.
Its internal components are the ranges of the original inclusions. This leaf
fixes no new Rees action: that action is supplied by the geometric comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory DirectSum
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A) (p : ℕ)

/-- The original degree-`p` cohomology of the actual `n`th ideal multiple. -/
abbrev idealPowerCohomology (n : ℕ) : ModuleCat.{u + 1} A :=
  (moduleCohomologyFunctorOfHom X α p).obj (idealPower X α F I n)

/-- The native direct sum of the original ideal-power cohomology modules. -/
abbrev idealPowerCohomologyTotal := ⨁ n : ℕ, idealPowerCohomology X α F I p n

/-- The canonical internal homogeneous component in the actual direct sum. -/
def idealPowerCohomologyComponent (n : ℕ) :
    Submodule A (idealPowerCohomologyTotal X α F I p) :=
  (DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) n).range

/-- Original cohomology identifies with its internal direct-sum component by inclusion. -/
def idealPowerCohomologyComponentEquiv (n : ℕ) :
    idealPowerCohomology X α F I p n ≃ₗ[A]
      idealPowerCohomologyComponent X α F I p n :=
  LinearEquiv.ofInjective (DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) n)
    (DirectSum.of_injective n)

@[simp]
theorem idealPowerCohomologyComponentEquiv_apply (n : ℕ)
    (x : idealPowerCohomology X α F I p n) :
    (idealPowerCohomologyComponentEquiv X α F I p n x).val =
      DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) n x := rfl

/-- The original direct-sum decomposition, expressed using its internal components. -/
instance idealPowerCohomologyComponentDecomposition :
    DirectSum.Decomposition (idealPowerCohomologyComponent X α F I p) := by
  let e := idealPowerCohomologyComponentEquiv X α F I p
  refine DirectSum.Decomposition.ofLinearMap
    (idealPowerCohomologyComponent X α F I p)
    (DirectSum.lmap (fun n => (e n).toLinearMap)) ?_ ?_
  · apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    simp [e]
  · apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (e n).surjective x
    simp [e]

/-- The internal degree-zero component identifies with original cohomology through
 the actual coefficient inclusion `I⁰F → F`. -/
def idealPowerCohomologyZeroEquiv :
    idealPowerCohomologyComponent X α F I p 0 ≃ₗ[A]
      (moduleCohomologyFunctorOfHom X α p).obj F :=
  (idealPowerCohomologyComponentEquiv X α F I p 0).symm.trans
    (((moduleCohomologyFunctorOfHom X α p).mapIso (idealPowerZeroIso X α F I)).toLinearEquiv)

/-- The degree-lowering original cohomology maps on internal homogeneous components. -/
def idealPowerCohomologyComponentMap {n m : ℕ} (h : m ≤ n) :
    idealPowerCohomologyComponent X α F I p n →ₗ[A]
      idealPowerCohomologyComponent X α F I p m :=
  (idealPowerCohomologyComponentEquiv X α F I p m).toLinearMap ∘ₗ
    ((moduleCohomologyFunctorOfHom X α p).map (idealPowerMap X α F I h)).hom ∘ₗ
      (idealPowerCohomologyComponentEquiv X α F I p n).symm.toLinearMap

/-- Lowering to degree zero and applying its canonical identification is the original
cohomology map of the coefficient inclusion into `F`. -/
theorem idealPowerCohomologyZeroEquiv_map (n : ℕ)
    (x : idealPowerCohomology X α F I p n) :
    idealPowerCohomologyZeroEquiv X α F I p
      (idealPowerCohomologyComponentMap X α F I p (Nat.zero_le n)
        (idealPowerCohomologyComponentEquiv X α F I p n x)) =
      moduleCohomologyMapOfHom X α (idealMultipleι X α F (I ^ n)) p x := by
  let H := moduleCohomologyFunctorOfHom X α p
  simp only [idealPowerCohomologyComponentMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, idealPowerCohomologyZeroEquiv,
    LinearEquiv.trans_apply]
  change H.map (idealMultipleι X α F (I ^ 0))
    (H.map (idealPowerMap X α F I (Nat.zero_le n)) x) = H.map _ x
  rw [← ModuleCat.comp_apply, ← H.map_comp, idealMultipleMap_ι]

end AlgebraicGeometry.Scheme.Cohomology
