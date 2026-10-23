/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Exchange

/-! # Canonical finite base change on the original derived and higher direct images

The morphisms are the original derived mate and its original higher-degree
transports. Exactness and ordinary exchange are supplied by actual finite
geometry, not by additional comparison hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  [IsFinite f] (h : IsPullback g' f' f g)

/-- Finite base change for the original bounded-below derived exchange, with
four independent derived-category universe inputs. -/
theorem finiteDerivedBaseChange_isIso :
    IsIso (derivedBaseChangeMap f f' g g' h.w.symm) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let := finiteBaseChange_isIso f f' g g' h
  exact isIso_derivedBaseChangeMap_of_exact f f' g g' h.w.symm

/-- Finite base change in every degree for the original higher exchange map. -/
theorem finiteHigherBaseChange_isIso (q : ℕ) :
    IsIso (higherBaseChangeMap f f' g g' h.w.symm q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let := finiteBaseChange_isIso f f' g g' h
  exact isIso_higherBaseChangeMap_of_exact f f' g g' h.w.symm q

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
