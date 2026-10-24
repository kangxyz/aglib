/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact

/-! # Naturality of the original native module localization sequence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)

/-- Every original coefficient map gives the actual localization diagram. -/
def moduleLocalizationShortComplexMap {F G : ModuleSheaf X Λ} (a : F ⟶ G) :
    moduleLocalizationShortComplex j Λ i hcomp F ⟶
      moduleLocalizationShortComplex j Λ i hcomp G where
  τ₁ := (moduleLowerShriek j Λ).map ((moduleInverseImage j Λ).map a)
  τ₂ := a
  τ₃ := (moduleDirectImage i Λ).map ((moduleInverseImage i Λ).map a)
  comm₁₂ := (moduleLowerShriekAdjunction j Λ).counit.naturality a
  comm₂₃ := (moduleInverseImageAdjunction i Λ).unit.naturality a

/-- Localization with its original arrows is functorial in the coefficient sheaf. -/
def moduleLocalizationShortComplexFunctor :
    ModuleSheaf X Λ ⥤ ShortComplex (ModuleSheaf X Λ) where
  obj F := moduleLocalizationShortComplex j Λ i hcomp F
  map a := moduleLocalizationShortComplexMap j Λ i hcomp a
  map_id F := by
    apply ShortComplex.hom_ext <;>
      simp [moduleLocalizationShortComplexMap, moduleLocalizationShortComplex]
  map_comp a b := by
    apply ShortComplex.hom_ext <;>
      simp [moduleLocalizationShortComplexMap, moduleLocalizationShortComplex]

end AlgebraicGeometry.Scheme.EtaleCohomology
