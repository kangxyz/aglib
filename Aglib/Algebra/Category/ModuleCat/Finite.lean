/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
/-!
# Finite modules over a noetherian ring

The object property here is genuine finite generation of modules. Over a
noetherian ring it is a Serre class, so its full subcategory is abelian. This
provides the algebraic affine chart for coherent sheaves, rather than assuming
an abelian structure on a category given an unrelated name.
-/
@[expose] public section


noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- The property of being a finitely generated `R`-module. -/
abbrev finiteModule : ObjectProperty (ModuleCat.{v} R) := ModuleCat.isFG R

/-- The actual full subcategory of finitely generated modules. -/
abbrev FiniteModule := FGModuleCat.{v} R

instance finiteModule_isoClosed : (finiteModule.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let : Module.Finite R _ := h
    exact Module.Finite.equiv e.toLinearEquiv

instance finiteModule_containsZero : (finiteModule.{u, v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R (ULift.{v} PUnit),
    ModuleCat.isZero_of_subsingleton _, by dsimp [finiteModule, ModuleCat.isFG]; infer_instance⟩

instance finiteModule_quotients : (finiteModule.{u, v} R).IsClosedUnderQuotients where
  prop_of_epi f hf h := by
    let : Module.Finite R _ := h
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

instance finiteModule_extensions : (finiteModule.{u, v} R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    let : Module.Finite R _ := h₁
    let : Module.Finite R _ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_surjective_g

variable [IsNoetherianRing R]

instance finiteModule_subobjects : (finiteModule.{u, v} R).IsClosedUnderSubobjects where
  prop_of_mono f hf h := by
    let : Module.Finite R _ := h
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp hf)

/-- Finite modules form a Serre class over a noetherian ring. -/
instance finiteModule_isSerreClass : (finiteModule.{u, v} R).IsSerreClass where

/-- Its exact structure consists of all short exact sequences. -/
def finiteModuleExactStructure : ExactStructure (FiniteModule.{u, v} R) :=
  abelianExactStructure _

end ModuleCat
