/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
/-!
# Localization of actual finite modules

The functor constructed here is the restriction of mathlib's module localization
functor to finitely generated modules. Over a noetherian ring it is exact, and
its kernel is the Serre class of modules killed by localization.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.FiniteLocalization

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Actual scalar localization on finitely generated modules. -/
def functor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} (Localization S) :=
  ObjectProperty.lift _
    (forget₂ (FGModuleCat R) (ModuleCat R) ⋙ ModuleCat.localizedModuleFunctor S)
    (fun M ↦ by
      change Module.Finite (Localization S) (M.obj.localizedModule S)
      exact Module.Finite.of_isLocalizedModule S (M.obj.localizedModuleMkLinearMap S))

@[simp] theorem functor_obj_obj (M : FGModuleCat.{u} R) :
    ((functor S).obj M).obj = M.obj.localizedModule S := rfl

@[simp] theorem functor_map_hom {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    ((functor S).map f).hom = ModuleCat.localizedModuleMap S f.hom := rfl

/-- The finite-module functor agrees with localization after forgetting finiteness. -/
theorem functor_comp_forget :
    functor S ⋙ forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S)) =
      forget₂ (FGModuleCat R) (ModuleCat R) ⋙ ModuleCat.localizedModuleFunctor S := rfl

instance functor_additive : (functor S).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.localizedModuleFunctor S).map_add

instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S) := by
  have : PreservesFiniteColimits
      (functor S ⋙ forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S))) := by
    rw [functor_comp_forget]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (functor S)
    (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S)))

variable [IsNoetherianRing R]

instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S) := by
  have : PreservesFiniteLimits
      (functor S ⋙ forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S))) := by
    rw [functor_comp_forget]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (functor S)
    (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S)))

/-- Finite modules whose actual localization vanishes. -/
def torsion : ObjectProperty (FGModuleCat.{u} R) := (functor S).kernel

instance torsion_isSerreClass : (torsion S).IsSerreClass := by
  dsimp [torsion]
  infer_instance

omit [IsNoetherianRing R] in
@[simp] theorem torsion_iff (M : FGModuleCat.{u} R) :
    torsion S M ↔ IsZero ((functor S).obj M) := Iff.rfl

/-- The denominators of the Serre quotient are exactly the localization isomorphisms. -/
theorem isoModSerre_iff {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (torsion S).isoModSerre f ↔ IsIso ((functor S).map f) := by
  change (functor S).kernel.isoModSerre f ↔ _
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  rfl

omit [IsNoetherianRing R] in
/-- Vanishing after localization is the usual elementwise torsion condition. -/
theorem torsion_iff_elementwise (M : FGModuleCat.{u} R) :
    torsion S M ↔ ∀ m : M, ∃ s ∈ S, s • m = 0 := by
  rw [torsion_iff]
  have hzero : IsZero ((functor S).obj M) ↔ IsZero (((functor S).obj M).obj) :=
    ⟨fun h ↦ (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S))).map_isZero h,
      fun h ↦ IsZero.of_full_of_faithful_of_isZero
        (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S))) _ h⟩
  rw [hzero, ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (M.obj.localizedModule S) ↔ _
  exact IsLocalizedModule.subsingleton_iff S (M.obj.localizedModuleMkLinearMap S)

omit [IsNoetherianRing R] in
/-- For a principal open, the kernel consists exactly of elementwise power torsion. -/
theorem torsion_powers_iff_elementwise (f : R) (M : FGModuleCat.{u} R) :
    torsion (Submonoid.powers f) M ↔ ∀ m : M, ∃ n : ℕ, f ^ n • m = 0 := by
  rw [torsion_iff_elementwise]
  simp only [Submonoid.mem_powers_iff, exists_exists_eq_and]

omit [IsNoetherianRing R] in
/-- Finite generation makes the torsion condition uniform: one denominator
annihilates the whole module. -/
theorem torsion_iff_uniform (M : FGModuleCat.{u} R) :
    torsion S M ↔ ∃ s : S, ∀ m : M, (s : R) • m = 0 := by
  constructor
  · intro h
    have hz : Subsingleton (M.obj.localizedModule S) := by
      apply (IsLocalizedModule.subsingleton_iff S (M.obj.localizedModuleMkLinearMap S)).2
      exact (torsion_iff_elementwise S M).1 h
    let := hz
    obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
      (M.obj.localizedModuleMkLinearMap S) (LinearMap.id : M →ₗ[R] M) 0
      (Subsingleton.elim _ _)
    refine ⟨s, fun m ↦ ?_⟩
    simpa only [Submonoid.smul_def, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.zero_apply, smul_zero] using LinearMap.congr_fun hs m
  · rintro ⟨s, hs⟩
    exact (torsion_iff_elementwise S M).2 fun m ↦ ⟨s, s.property, hs m⟩

omit [IsNoetherianRing R] in
/-- A finite module vanishes on the principal open exactly when one power
of its defining element annihilates every section of the module. -/
theorem torsion_powers_iff_uniform (f : R) (M : FGModuleCat.{u} R) :
    torsion (Submonoid.powers f) M ↔ ∃ n : ℕ, ∀ m : M, f ^ n • m = 0 := by
  rw [torsion_iff_uniform]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩

end ModuleCat.FiniteLocalization
