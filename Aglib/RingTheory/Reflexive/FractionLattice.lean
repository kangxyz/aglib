/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.Localization
public import Mathlib.RingTheory.Localization.FractionRing

/-! Recovery of a reflexive lattice from integral values of its actual localized dual. -/

@[expose] public section

noncomputable section

namespace Module

variable {R K M Mₖ : Type*} [CommRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup Mₖ] [Module R Mₖ]
  [Module K Mₖ] [IsScalarTower R K Mₖ]
  [FinitePresentation R M] [FinitePresentation R (Dual R M)] [IsReflexive R M]

/-- A generic vector belongs to a reflexive module exactly when all its original dual
functionals have integral values. The generic dual map is the canonical localization map. -/
theorem IsReflexive.mem_range_of_dual (f : M →ₗ[R] Mₖ)
    [IsLocalizedModule (nonZeroDivisors R) f] (x : Mₖ)
    (hx : ∀ l : Dual R M,
      IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K l x ∈
        Set.range (algebraMap R K)) : x ∈ Set.range f := by
  classical
  let S := nonZeroDivisors R
  let d : Dual R M →ₗ[R] Dual K Mₖ :=
    IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R K) K
  let e : Dual R M →ₗ[R] K := ((Dual.eval K Mₖ x).restrictScalars R).comp d
  choose v hv using hx
  have hv' (l : Dual R M) : algebraMap R K (v l) = e l := hv l
  let g : Dual R (Dual R M) :=
    { toFun := v
      map_add' := fun l t ↦ (IsFractionRing.injective R K) (by
        simp only [map_add, hv'])
      map_smul' := fun r l ↦ (IsFractionRing.injective R K) (by
        change algebraMap R K (v (r • l)) = algebraMap R K (r * v l)
        simp only [map_mul, hv', map_smul, Algebra.smul_def]) }
  let m := (evalEquiv R M).symm g
  refine ⟨m, ?_⟩
  let := IsReflexive.of_isLocalizedModule S K f
  apply (bijective_dual_eval K Mₖ).1
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S d (Algebra.linearMap R K)
  apply LinearMap.ext
  intro l
  change IsLocalizedModule.map S f (Algebra.linearMap R K) l (f m) = d l x
  rw [IsLocalizedModule.map_apply]
  change algebraMap R K (l ((evalEquiv R M).symm g)) = e l
  rw [apply_evalEquiv_symm_apply]
  exact hv' l

end Module
