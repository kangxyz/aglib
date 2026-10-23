/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Coefficient retracts of the original exchange

Naturality makes the original exchange at a coefficient retract an actual
arrow retract of the original exchange at the larger coefficient. Native
stability of isomorphisms under retracts gives the derived and all-degree
conclusions, retaining the original coefficient maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The actual derived exchange is invertible on any specified coefficient
retract of a coefficient where the same original exchange is invertible. -/
theorem derivedBaseChangeMap_isIso_of_retract
    {K L : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)} (r : Retract K L)
    [IsIso ((derivedBaseChangeMap f f' g g' h).app L)] :
    IsIso ((derivedBaseChangeMap f f' g g' h).app K) :=
  MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    ((derivedBaseChangeMap f f' g g' h).retractArrowApp r) inferInstance

/-- The original exchange on every higher direct image preserves actual
coefficient retracts, with no change to either original sheaf morphism. -/
theorem higherBaseChangeMap_isIso_of_retract
    {F G : AbelianSheaf.{u, u + 1} X} (r : Retract F G) (q : ℕ)
    [IsIso ((higherBaseChangeMap f f' g g' h q).app G)] :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) :=
  MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    ((higherBaseChangeMap f f' g g' h q).retractArrowApp r) inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
