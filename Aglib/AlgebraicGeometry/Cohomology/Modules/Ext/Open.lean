/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison

/-!
# Original module-open Ext and native open cohomology

The native module open-free generator and the native integer open-free
generator represent the same original sections. Exact scalar forgetting and
their original generator map compare their Ext groups. Images of module
injectives are flasque, so the comparison is bijective in every degree.
The actual coefficient maps, restriction maps and scalar actions are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) (U : X.Opens)

/-- The actual integer-open generator represents the original module-open universal section. -/
def moduleOpenIntegerMap : (additiveOpenFreeFunctor X).obj U ⟶
    moduleAddSheaf X (Scheme.Modules.openFree X U) :=
  (additiveOpenHomEquiv X U _).symm
    (Scheme.Modules.openFreeHomEquiv X U _ (𝟙 (Scheme.Modules.openFree X U)))

theorem moduleOpenIntegerMap_sections :
    additiveOpenHomEquiv X U (moduleAddSheaf X (Scheme.Modules.openFree X U))
        (moduleOpenIntegerMap X U) =
      Scheme.Modules.openFreeHomEquiv X U _ (𝟙 (Scheme.Modules.openFree X U)) :=
  Equiv.apply_symm_apply _ _

/-- The two original Hom functors represent the same sections on the indicated open. -/
def moduleOpenIntegerHomEquiv (M : X.Modules) :
    (Scheme.Modules.openFree X U ⟶ M) ≃
      ((additiveOpenFreeFunctor X).obj U ⟶ moduleAddSheaf X M) :=
  (Scheme.Modules.openFreeHomEquiv X U M).trans
    (additiveOpenHomEquiv X U (moduleAddSheaf X M)).symm

/-- The original section comparison is exact forgetting followed by the actual generator. -/
theorem moduleOpenIntegerHomEquiv_apply (M : X.Modules)
    (f : Scheme.Modules.openFree X U ⟶ M) :
    moduleOpenIntegerHomEquiv X U M f =
      moduleOpenIntegerMap X U ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f := by
  apply (additiveOpenHomEquiv X U (moduleAddSheaf X M)).injective
  change additiveOpenHomEquiv X U (moduleAddSheaf X M)
      ((additiveOpenHomEquiv X U (moduleAddSheaf X M)).symm
        (Scheme.Modules.openFreeHomEquiv X U M f)) = _
  rw [Equiv.apply_symm_apply, additiveOpenHomEquiv_naturality_coefficient,
    moduleOpenIntegerMap_sections]
  change Scheme.Modules.openFreeHomEquiv X U M f =
    f.app U (Scheme.Modules.openFreeHomEquiv X U _ (𝟙 (Scheme.Modules.openFree X U)))
  simpa only [Category.id_comp] using
    Scheme.Modules.openFreeHomEquiv_comp X U (𝟙 (Scheme.Modules.openFree X U)) f

/-- The original module-open Ext comparison to the unchanged native `Sheaf.H'`. -/
def moduleOpenExtCohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{u + 1} (Scheme.Modules.openFree X U) M n →+
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U :=
  (SheafOfModules.toSheaf.{u} X.ringCatSheaf).extPrecompMap (moduleOpenIntegerMap X U) M n

theorem moduleOpenExtCohomologyMap_apply (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X U) M n) :
    moduleOpenExtCohomologyMap X U M n x =
      (Ext.mk₀ (moduleOpenIntegerMap X U)).comp
        (x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) (Nat.zero_add n) := rfl

theorem moduleOpenExtCohomologyMap_mk₀ (M : X.Modules)
    (f : Scheme.Modules.openFree X U ⟶ M) :
    moduleOpenExtCohomologyMap X U M 0 (Ext.mk₀ f) =
      Ext.mk₀ (moduleOpenIntegerMap X U ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  exact Functor.extPrecompMap_mk₀ F (moduleOpenIntegerMap X U) f

theorem moduleOpenExtCohomologyMap_bijective_zero (M : X.Modules) :
    Function.Bijective (moduleOpenExtCohomologyMap X U M 0) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (Scheme.Modules.openFree X U) M).surjective x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (Scheme.Modules.openFree X U) M).surjective y
    rw [moduleOpenExtCohomologyMap_mk₀, moduleOpenExtCohomologyMap_mk₀] at hxy
    have hfg : moduleOpenIntegerHomEquiv X U M f = moduleOpenIntegerHomEquiv X U M g := by
      simpa only [moduleOpenIntegerHomEquiv_apply] using
        (Ext.mk₀_bijective _ _).injective hxy
    exact congrArg Ext.mk₀ ((moduleOpenIntegerHomEquiv X U M).injective hfg)
  · intro x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨f, hf⟩ := (moduleOpenIntegerHomEquiv X U M).surjective g
    refine ⟨Ext.mk₀ f, ?_⟩
    rw [moduleOpenExtCohomologyMap_mk₀, ← moduleOpenIntegerHomEquiv_apply, hf]

/-- Module injectives are acyclic on every open for the original native open cohomology. -/
theorem subsingleton_moduleHPrime_of_injective (M : X.Modules) [Injective M] (n : ℕ) :
    Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) (n + 1) U) := by
  let : TopCat.Presheaf.IsFlasque (moduleAddSheaf X M).obj :=
    Scheme.Modules.injective_isFlasque X M
  exact subsingleton_sheafHPrime_of_isFlasque U _ n

/-- Actual exact forgetting computes the original native open cohomology in every degree. -/
theorem moduleOpenExtCohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (moduleOpenExtCohomologyMap X U M n) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  exact Functor.extPrecompMap_bijective_of_acyclic_injectives F (moduleOpenIntegerMap X U)
    (moduleOpenExtCohomologyMap_bijective_zero X U)
    (fun I _ n ↦ subsingleton_moduleHPrime_of_injective X U I n) M n

/-- The additive equivalence retains the original generator/forgetting forward map. -/
def moduleOpenExtCohomologyAddEquiv (M : X.Modules) (n : ℕ) :
    Ext.{u + 1} (Scheme.Modules.openFree X U) M n ≃+
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U :=
  AddEquiv.ofBijective (moduleOpenExtCohomologyMap X U M n)
    (moduleOpenExtCohomologyMap_bijective X U M n)

theorem moduleOpenExtCohomologyMap_yoneda {M N : X.Modules} {i j k : ℕ}
    (x : Ext.{u + 1} (Scheme.Modules.openFree X U) M i)
    (y : Ext.{u + 1} M N j) (h : i + j = k) :
    moduleOpenExtCohomologyMap X U N k (x.comp y h) =
      (moduleOpenExtCohomologyMap X U M i x).comp
        (y.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) h := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  exact Functor.extPrecompMap_comp F (moduleOpenIntegerMap X U) x y h

/-- Original module coefficient maps become the unchanged native open-cohomology maps. -/
theorem moduleOpenExtCohomologyMap_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X U) M n) :
    moduleOpenExtCohomologyMap X U N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f)).app (op U))
          (moduleOpenExtCohomologyMap X U M n x) := by
  rw [moduleOpenExtCohomologyMap_yoneda, Ext.mapExactFunctor_mk₀]
  rfl

variable {U} {V : X.Opens} (i : U ⟶ V)

/-- Both native open-free generators retain the original open restriction. -/
theorem moduleOpenIntegerMap_naturality :
    (additiveOpenFreeFunctor X).map i ≫ moduleOpenIntegerMap X V =
      moduleOpenIntegerMap X U ≫
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
          ((Scheme.Modules.openFreeFunctor X).map i) := by
  apply (additiveOpenHomEquiv X U _).injective
  rw [additiveOpenHomEquiv_naturality, additiveOpenHomEquiv_naturality_coefficient,
    moduleOpenIntegerMap_sections, moduleOpenIntegerMap_sections]
  have h₁ := Scheme.Modules.openFreeHomEquiv_naturality_open X i
    (Scheme.Modules.openFree X V) (𝟙 _)
  have h₂ := Scheme.Modules.openFreeHomEquiv_comp X U (𝟙 (Scheme.Modules.openFree X U))
    ((Scheme.Modules.openFreeFunctor X).map i)
  let φ : Scheme.Modules.openFree X U ⟶ Scheme.Modules.openFree X V :=
    (Scheme.Modules.openFreeFunctor X).map i
  change Scheme.Modules.openFreeHomEquiv X U (Scheme.Modules.openFree X V)
    (φ ≫ 𝟙 (Scheme.Modules.openFree X V)) = _ at h₁
  change Scheme.Modules.openFreeHomEquiv X U (Scheme.Modules.openFree X V)
    (𝟙 (Scheme.Modules.openFree X U) ≫ φ) = _ at h₂
  rw [Category.comp_id] at h₁
  rw [Category.id_comp] at h₂
  exact h₁.symm.trans h₂

/-- Original module-open Ext restriction is the original native cohomology-presheaf restriction. -/
theorem moduleOpenExtCohomologyMap_restriction (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X V) M n) :
    moduleOpenExtCohomologyMap X U M n
        ((Ext.mk₀ ((Scheme.Modules.openFreeFunctor X).map i)).comp x (Nat.zero_add n)) =
      (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n).map i.op
        (moduleOpenExtCohomologyMap X V M n x) := by
  change moduleOpenExtCohomologyMap X U M n
      ((Ext.mk₀ ((Scheme.Modules.openFreeFunctor X).map i)).comp x (Nat.zero_add n)) =
    (Ext.mk₀ ((additiveOpenFreeFunctor X).map i)).comp
      (moduleOpenExtCohomologyMap X V M n x) (Nat.zero_add n)
  rw [moduleOpenExtCohomologyMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    moduleOpenExtCohomologyMap_apply, ← Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
    moduleOpenIntegerMap_naturality]

/-- Forgetting original module-linear global multiplication is actual additive multiplication. -/
theorem moduleGlobalScalar_toAddSheaf (M : X.Modules) (a : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map
        (Scheme.Modules.globalScalarEndomorphism X M a) = moduleScalarOfGlobal X M a := by
  ext V x
  exact Scheme.Modules.globalScalarEndomorphism_app X M a V.unop x

variable (U)

/-- Native linear-category Ext on the actual module-open source computes original `H'`
linearly with its original coefficient scalar action. -/
def moduleOpenExtCohomologyLinearEquiv {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom X α
    letI := moduleHPrimeModuleOfHom X α M n U
    Ext.{u + 1} (Scheme.Modules.openFree X U) M n ≃ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U := by
  letI := Scheme.Modules.moduleCategoryLinearOfHom X α
  letI := moduleHPrimeModuleOfHom X α M n U
  refine { __ := moduleOpenExtCohomologyAddEquiv X U M n, map_smul' := fun r x ↦ ?_ }
  change moduleOpenExtCohomologyMap X U M n (r • x) =
    (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      (moduleScalarOfGlobal X M (α r))).app (op U)) (moduleOpenExtCohomologyMap X U M n x)
  rw [moduleExt_smul_postcomp_of_hom, moduleOpenExtCohomologyMap_naturality,
    moduleGlobalScalar_toAddSheaf]

/-- The original module-open universal morphism representing one of the structure module. -/
def moduleOpenTopUnitMap : Scheme.Modules.openFree X ⊤ ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.openFreeHomEquiv X ⊤ _).symm (1 : Γ(X, ⊤))

/-- The native top-open generator becomes the original constant-integer generator one. -/
theorem moduleOpenIntegerMap_top :
    (additiveOpenTopIsoInteger X).inv ≫ moduleOpenIntegerMap X ⊤ ≫
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (moduleOpenTopUnitMap X) =
      moduleUnitIntegerMap X := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := moduleAddSheaf X O
  let C : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have hl : additiveOpenHomEquiv X ⊤ A
      (moduleOpenIntegerMap X ⊤ ≫
        F.map (moduleOpenTopUnitMap X)) =
      (1 : Γ(X, ⊤)) := by
    rw [← moduleOpenIntegerHomEquiv_apply]
    change (additiveOpenHomEquiv X ⊤ A)
      ((additiveOpenHomEquiv X ⊤ A).symm
        ((Scheme.Modules.openFreeHomEquiv X ⊤ O)
          ((Scheme.Modules.openFreeHomEquiv X ⊤ O).symm (1 : Γ(X, ⊤))))) = (1 : Γ(X, ⊤))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hr : additiveOpenHomEquiv X ⊤ A
      ((additiveOpenTopIsoInteger X).hom ≫ moduleUnitIntegerMap X) = (1 : Γ(X, ⊤)) := by
    rw [additiveOpenHomEquiv_naturality_coefficient]
    change (moduleUnitIntegerMap X).hom.app (op ⊤)
      ((additiveOpenHomEquiv X ⊤ C)
        ((additiveOpenHomEquiv X ⊤ C).symm (integerSheafHomEquiv C (𝟙 C)))) = (1 : Γ(X, ⊤))
    rw [Equiv.apply_symm_apply, ← integerSheafHomEquiv_comp, Category.id_comp,
      moduleUnitIntegerMap_sections]
  have h : moduleOpenIntegerMap X ⊤ ≫ F.map (moduleOpenTopUnitMap X) =
      (additiveOpenTopIsoInteger X).hom ≫ moduleUnitIntegerMap X :=
    (additiveOpenHomEquiv X ⊤ A).injective (hl.trans hr.symm)
  change (additiveOpenTopIsoInteger X).inv ≫
    (moduleOpenIntegerMap X ⊤ ≫ F.map (moduleOpenTopUnitMap X)) = moduleUnitIntegerMap X
  rw [h]
  simp

/-- At the top, the open Ext comparison is exactly the original structure-module Ext
comparison, using the original whole-space cohomology normalization. -/
theorem moduleOpenExtCohomologyMap_top (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) n
        (moduleOpenExtCohomologyMap X ⊤ M n
          ((Ext.mk₀ (moduleOpenTopUnitMap X)).comp x (Nat.zero_add n))) =
      moduleExtCohomologyMap X M n x := by
  change (Ext.mk₀ (additiveOpenTopIsoInteger X).inv).comp
      (moduleOpenExtCohomologyMap X ⊤ M n
        ((Ext.mk₀ (moduleOpenTopUnitMap X)).comp x (Nat.zero_add n))) (Nat.zero_add n) = _
  rw [moduleOpenExtCohomologyMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    moduleExtCohomologyMap_apply]
  simp only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [moduleOpenIntegerMap_top]

end AlgebraicGeometry.Scheme.Cohomology
