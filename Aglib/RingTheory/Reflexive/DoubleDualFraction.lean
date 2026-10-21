/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-! The actual double dual embedded in the generic fibre, without assuming reflexivity. -/

@[expose] public section

noncomputable section

namespace Module.Dual

variable {R K M Mₖ : Type*} [CommRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup Mₖ] [Module R Mₖ]
  [Module K Mₖ] [IsScalarTower R K Mₖ]
  [FinitePresentation R M] [IsReflexive K Mₖ]
  (f : M →ₗ[R] Mₖ) [IsLocalizedModule (nonZeroDivisors R) f]

/-- Embed the original double dual into the generic fibre using the canonical two dual
localization maps and generic evaluation. No reflexivity over the original ring is assumed. -/
def doubleDualToFraction : Dual R (Dual R M) →ₗ[R] Mₖ :=
  ((evalEquiv K Mₖ).symm.restrictScalars R).toLinearMap.comp
    (IsLocalizedModule.mapExtendScalars (nonZeroDivisors R)
      (IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K)
      (Algebra.linearMap R K) K)

/-- Evaluating a localized dual on the embedded double dual recovers the original pairing. -/
theorem doubleDualToFraction_apply_dual (g : Dual R (Dual R M)) (l : Dual R M) :
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K l
      (doubleDualToFraction (K := K) f g) = algebraMap R K (g l) := by
  let d := IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K
  change d l ((evalEquiv K Mₖ).symm
    (IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) d (Algebra.linearMap R K) K g)) = _
  rw [apply_evalEquiv_symm_apply]
  exact IsLocalizedModule.map_apply (nonZeroDivisors R) d (Algebra.linearMap R K) g l

/-- The generic embedding of the double dual is injective. -/
theorem doubleDualToFraction_injective : Function.Injective (doubleDualToFraction (K := K) f) := by
  intro g h he
  apply LinearMap.ext
  intro l
  apply IsFractionRing.injective R K
  rw [← doubleDualToFraction_apply_dual f g l, ← doubleDualToFraction_apply_dual f h l, he]

/-- The embedded original evaluation is the original generic localization map. -/
@[simp]
theorem doubleDualToFraction_eval (m : M) : doubleDualToFraction (K := K) f (eval R M m) = f m := by
  let S := nonZeroDivisors R
  let d := IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R K) K
  apply (bijective_dual_eval K Mₖ).injective
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S d (Algebra.linearMap R K)
  apply LinearMap.ext
  intro l
  change d l (doubleDualToFraction (K := K) f (eval R M m)) = d l (f m)
  rw [doubleDualToFraction_apply_dual]
  exact (IsLocalizedModule.map_apply S f (Algebra.linearMap R K) l m).symm

/-- The image of the double dual consists exactly of vectors on which every original dual
functional takes values in the original ring. -/
theorem mem_range_doubleDualToFraction_iff (x : Mₖ) :
    x ∈ Set.range (doubleDualToFraction (K := K) f) ↔
      ∀ l : Dual R M,
        IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K l x ∈
          Set.range (algebraMap R K) := by
  constructor
  · rintro ⟨g, rfl⟩ l
    exact ⟨g l, (doubleDualToFraction_apply_dual f g l).symm⟩
  · intro hx
    classical
    let S := nonZeroDivisors R
    let d := IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R K) K
    let e : Dual R M →ₗ[R] K := ((eval K Mₖ x).restrictScalars R).comp d
    let g : Dual R (Dual R M) := e.codRestrictOfInjective (Algebra.linearMap R K)
      (IsFractionRing.injective R K) hx
    have hg (l : Dual R M) : algebraMap R K (g l) = e l :=
      LinearMap.codRestrictOfInjective_comp_apply e (Algebra.linearMap R K)
        (IsFractionRing.injective R K) hx l
    refine ⟨g, ?_⟩
    apply (bijective_dual_eval K Mₖ).injective
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S d (Algebra.linearMap R K)
    apply LinearMap.ext
    intro l
    change d l (doubleDualToFraction (K := K) f g) = d l x
    rw [doubleDualToFraction_apply_dual]
    exact hg l

end Module.Dual
