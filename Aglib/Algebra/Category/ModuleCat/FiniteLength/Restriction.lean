/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FiniteLength.Support
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Module

/-!
# Surjectivity of module localization at units and finite length after restriction along a
surjective ring map.

Source: `lean/R5Lab/Aglib/Algebra/Category/ModuleCat/FiniteLength/Restriction.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `a43905c72f38772c552a03f562bb2d7d7e39288c5a81959df0643394f255a364`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace ModuleCat
universe u v
/-- Localization at units is surjective on modules, with the original localization map. -/
theorem localizedModule_surjective_of_units
    {R : Type u} [CommRing R] {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (hS : ∀ s : S, IsUnit (s : R)) : Function.Surjective f := by
  intro y
  obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.surj S f y
  obtain ⟨a, ha⟩ := hS s
  refine ⟨(↑(a⁻¹) : R) • m, ?_⟩
  rw [f.map_smul, ← hm]
  change (↑(a⁻¹) : R) • ((s : R) • y) = y
  rw [← ha, smul_smul, Units.inv_mul, one_smul]

/-- Finite length survives restriction along a surjective ring map, with its actual action. -/
theorem finiteLength_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} S)
    (hM : IsFiniteLength S M) : IsFiniteLength R ((ModuleCat.restrictScalars f).obj M) := by
  let : RingHomSurjective f := ⟨hf⟩
  let e : ((ModuleCat.restrictScalars f).obj M) →ₛₗ[f] M :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hM ⊢
  exact ⟨(e.isNoetherian_iff_of_bijective Function.bijective_id).mpr hM.1,
    (e.isArtinian_iff_of_bijective Function.bijective_id).mpr hM.2⟩

end ModuleCat
