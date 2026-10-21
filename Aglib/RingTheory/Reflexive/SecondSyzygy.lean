/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite reflexive modules as second syzygies

Dualizing a finite free presentation of the dual of a finite reflexive module
exhibits the original module as a kernel between finite free modules. The
identification uses the native bidual evaluation equivalence. No regularity,
normality, or projective-dimension hypothesis is needed for this construction.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module

/-- A finite reflexive module over a Noetherian commutative ring is a second
syzygy of finite free modules. Exactness refers to the exhibited linear maps. -/
theorem exists_finite_free_second_syzygy (R : Type u) (M : Type v)
    [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsReflexive R M] :
    ∃ (F₀ F₁ : Type u) (_ : AddCommGroup F₀) (_ : Module R F₀)
      (_ : Module.Free R F₀) (_ : Module.Finite R F₀)
      (_ : AddCommGroup F₁) (_ : Module R F₁)
      (_ : Module.Free R F₁) (_ : Module.Finite R F₁)
      (f : M →ₗ[R] F₀) (g : F₀ →ₗ[R] F₁),
      Function.Injective f ∧ LinearMap.range f = LinearMap.ker g := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R (Module.Dual R M)
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R (LinearMap.ker p)
  let g₀ : (Fin m → R) →ₗ[R] (Fin n → R) := (LinearMap.ker p).subtype.comp q
  have hg₀ : LinearMap.range g₀ = LinearMap.ker p := by
    dsimp [g₀]
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hq),
      Submodule.range_subtype]
  let f : M →ₗ[R] Module.Dual R (Fin n → R) :=
    p.dualMap.comp (Module.evalEquiv R M).toLinearMap
  refine ⟨Module.Dual R (Fin n → R), Module.Dual R (Fin m → R),
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, f, g₀.dualMap, ?_, ?_⟩
  · exact (LinearMap.dualMap_injective_of_surjective hp).comp
      (Module.evalEquiv R M).injective
  · dsimp [f]
    rw [LinearMap.range_comp_of_range_eq_top _ (Module.erange_coe R M),
      LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective p hp,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, hg₀]

end Module
