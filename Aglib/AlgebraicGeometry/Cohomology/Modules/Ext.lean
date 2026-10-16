/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Aglib.AlgebraicGeometry.Modules.Ext
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology

/-!
# Original module-linear Ext and actual additive-sheaf cohomology

The actual scalar-forgetting functor on Ext, precomposed with the original
constant-integer map representing one in the structure module, identifies
`Ext` from the structure module with the existing additive `Sheaf.H`.
Degree zero is the original unit-module/global-section comparison. Images
of module injectives are acyclic by their proved flasqueness; they are not
assumed to be injective additive sheaves. The original coefficient maps
and Yoneda composition are retained in every degree.
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

variable (X : Scheme.{u})

local instance : HasExt.{u + 1} (SheafOfModules.{u} X.ringCatSheaf) :=
  HasExt.standard _

/-- The original constant-integer map representing the section one of the structure module. -/
def moduleUnitIntegerMap :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf) :=
  (integerSheafHomEquiv _).symm (1 : Γ(X, ⊤))

/-- The original generator map represents the original section one. -/
theorem moduleUnitIntegerMap_sections :
    integerSheafHomEquiv (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf))
        (moduleUnitIntegerMap X) = (1 : Γ(X, ⊤)) :=
  AddEquiv.apply_symm_apply _ _

/-- The original unit-module and constant-integer Hom functors represent the same sections. -/
def moduleUnitIntegerHomEquiv (M : X.Modules) :
    ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) ≃
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ moduleAddSheaf X M) :=
  (Scheme.Modules.unitHomGlobalSectionsEquiv X M).trans
    (integerSheafHomEquiv (moduleAddSheaf X M)).symm.toEquiv

/-- The Hom comparison is exactly scalar forgetting followed by the original generator map. -/
theorem moduleUnitIntegerHomEquiv_apply (M : X.Modules)
    (f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    moduleUnitIntegerHomEquiv X M f =
      moduleUnitIntegerMap X ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f := by
  apply (integerSheafHomEquiv (moduleAddSheaf X M)).injective
  have he : integerSheafHomEquiv (moduleAddSheaf X M) (moduleUnitIntegerHomEquiv X M f) =
      Scheme.Modules.unitHomGlobalSectionsEquiv X M f :=
    AddEquiv.apply_symm_apply _ _
  rw [he, integerSheafHomEquiv_comp, moduleUnitIntegerMap_sections]
  rfl

/-- The canonical module Ext/cohomology map: actual exact scalar forgetting and generator one. -/
def moduleExtCohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n →+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  (SheafOfModules.toSheaf.{u} X.ringCatSheaf).extPrecompMap (moduleUnitIntegerMap X) M n

/-- The canonical comparison retains its literal original Ext formula. -/
theorem moduleExtCohomologyMap_apply (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    moduleExtCohomologyMap X M n x =
      (Ext.mk₀ (moduleUnitIntegerMap X)).comp
        (x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) (Nat.zero_add n) := rfl

/-- Degree-zero normalization uses the original module morphism and scalar-forgetting map. -/
theorem moduleExtCohomologyMap_mk₀ (M : X.Modules)
    (f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    moduleExtCohomologyMap X M 0 (Ext.mk₀ f) =
      Ext.mk₀ (moduleUnitIntegerMap X ≫ (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) :=
  Functor.extPrecompMap_mk₀ _ _ f

/-- The original canonical comparison is bijective in degree zero. -/
theorem moduleExtCohomologyMap_bijective_zero (M : X.Modules) :
    Function.Bijective (moduleExtCohomologyMap X M 0) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (SheafOfModules.unit X.ringCatSheaf) M).surjective x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (SheafOfModules.unit X.ringCatSheaf) M).surjective y
    rw [moduleExtCohomologyMap_mk₀, moduleExtCohomologyMap_mk₀] at hxy
    have hfg : moduleUnitIntegerHomEquiv X M f = moduleUnitIntegerHomEquiv X M g := by
      simpa only [moduleUnitIntegerHomEquiv_apply] using
        (Ext.mk₀_bijective _ _).injective hxy
    exact congrArg Ext.mk₀ ((moduleUnitIntegerHomEquiv X M).injective hfg)
  · intro x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨f, hf⟩ := (moduleUnitIntegerHomEquiv X M).surjective g
    refine ⟨Ext.mk₀ f, ?_⟩
    rw [moduleExtCohomologyMap_mk₀, ← moduleUnitIntegerHomEquiv_apply, hf]

/-- The original module-linear Ext comparison computes actual additive cohomology in all degrees. -/
theorem moduleExtCohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (moduleExtCohomologyMap X M n) :=
  Functor.extPrecompMap_bijective_of_acyclic_injectives
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) (moduleUnitIntegerMap X)
    (moduleExtCohomologyMap_bijective_zero X)
    (fun I _ n => subsingleton_moduleAddSheafH_of_injective I n) M n

/-- The canonical additive comparison between original module Ext and original Sheaf.H. -/
def moduleExtCohomologyAddEquiv (M : X.Modules) (n : ℕ) :
    Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  AddEquiv.ofBijective (moduleExtCohomologyMap X M n) (moduleExtCohomologyMap_bijective X M n)

/-- Original module Yoneda composition becomes original additive Yoneda composition. -/
theorem moduleExtCohomologyMap_yoneda {M N : X.Modules} {i j k : ℕ}
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M i)
    (y : Ext.{u + 1} M N j) (h : i + j = k) :
    moduleExtCohomologyMap X N k (x.comp y h) =
      (moduleExtCohomologyMap X M i x).comp
        (y.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) h :=
  Functor.extPrecompMap_comp _ _ x y h

/-- The original comparison retains the original module coefficient map. -/
theorem moduleExtCohomologyMap_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    moduleExtCohomologyMap X N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      Sheaf.H.map ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) n
        (moduleExtCohomologyMap X M n x) := by
  rw [moduleExtCohomologyMap_yoneda, Ext.mapExactFunctor_mk₀]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
