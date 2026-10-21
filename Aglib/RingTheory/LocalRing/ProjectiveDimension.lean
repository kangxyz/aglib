/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Length-one finite free resolutions over local rings

A finite module of projective dimension at most one over a Noetherian local
ring has a genuine short exact finite free resolution. The kernel of an
arbitrary finite free presentation is projective by dimension shifting, and
hence free by the local finite-projective criterion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ModuleCat

/-- Finite modules of projective dimension at most one over Noetherian local
rings admit actual short exact finite free resolutions. -/
theorem exists_finite_free_shortExact_of_projectiveDimension_le_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (hM : projectiveDimension M ≤ 1) :
    ∃ (P₁ P₀ : Type u) (_ : AddCommGroup P₁) (_ : Module R P₁)
      (_ : Module.Free R P₁) (_ : Module.Finite R P₁)
      (_ : AddCommGroup P₀) (_ : Module R P₀)
      (_ : Module.Free R P₀) (_ : Module.Finite R P₀)
      (f : P₁ →ₗ[R] P₀) (g : P₀ →ₗ[R] M),
      Function.Injective f ∧ Function.Surjective g ∧ Function.Exact f g := by
  obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
  let S := p.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
  have : HasProjectiveDimensionLE M 1 := (projectiveDimension_le_iff M 1).mp hM
  have : HasProjectiveDimensionLE S.X₁ 0 :=
    (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp inferInstance
  have : Projective S.X₁ :=
    (projective_iff_hasProjectiveDimensionLE_zero S.X₁).mpr inferInstance
  have : Module.Projective R (LinearMap.ker p) :=
    ModuleCat.projective_of_module_projective S.X₁
  have : Module.Free R (LinearMap.ker p) := Module.free_of_flat_of_isLocalRing
  exact ⟨LinearMap.ker p, P, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    (LinearMap.ker p).subtype, p, Subtype.val_injective, hp, p.exact_subtype_ker_map⟩

end ModuleCat
