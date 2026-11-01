/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConnectedTorsionSections
public import Aglib.CategoryTheory.Sites.SectionsAdditive

/-! # Actual module-valued derived global sections

Native constant-ring module sheaves are transported by the existing equivalence
to module-valued sheaves, then evaluated by the original global-section functor.
The derived functor is the installed bounded-below right-derived functor of
this actual composite; it is not a new derived carrier.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wΛ

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- Original module global sections, transported from genuine ringed coefficients. -/
def moduleGlobalSections : ModuleSheaf X Λ ⥤ ModuleCat.{u + 1} Λ :=
  (moduleSheafEquivalence X Λ).inverse ⋙
    Constructible.Modules.moduleGlobalSections Λ X

instance moduleGlobalSections_additive : (moduleGlobalSections X Λ).Additive := by
  let : (moduleSheafEquivalence X Λ).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  change ((moduleSheafEquivalence X Λ).inverse ⋙
    Constructible.Modules.moduleGlobalSections Λ X).Additive
  infer_instance

/-- Actual bounded-below derived global sections, with independent native models. -/
abbrev moduleDerivedGlobalSections
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)] :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  (moduleGlobalSections X Λ).rightDerivedFunctorPlus

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
