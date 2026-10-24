/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.AbelianShortExact

/-! # Naturality of the original abelian localization sequence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)

/-- Every original coefficient map gives the actual localization diagram. -/
def abelianLocalizationShortComplexMap {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) :
    abelianLocalizationShortComplex j i hcomp F ⟶
      abelianLocalizationShortComplex j i hcomp G where
  τ₁ := (etaleLowerShriek j).map ((inverseImage j).map a)
  τ₂ := a
  τ₃ := (directImage i).map ((inverseImage i).map a)
  comm₁₂ := (etaleLowerShriekAdjunction j).counit.naturality a
  comm₂₃ := (inverseImageAdjunction i).unit.naturality a

/-- Localization with its original arrows is functorial in the coefficient sheaf. -/
def abelianLocalizationShortComplexFunctor :
    AbelianSheaf.{u, u + 1} X ⥤ ShortComplex (AbelianSheaf.{u, u + 1} X) where
  obj F := abelianLocalizationShortComplex j i hcomp F
  map a := abelianLocalizationShortComplexMap j i hcomp a
  map_id F := by
    apply ShortComplex.hom_ext <;>
      simp [abelianLocalizationShortComplexMap, abelianLocalizationShortComplex]
  map_comp a b := by
    apply ShortComplex.hom_ext <;>
      simp [abelianLocalizationShortComplexMap, abelianLocalizationShortComplex]

end AlgebraicGeometry.Scheme.EtaleCohomology
