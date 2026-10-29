/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.EtaleDerived

/-! # Canonical smooth base change in relative dimension zero

The native equivalence between étaleness and smoothness of relative dimension
zero specializes the original-map étale theorem. No finiteness or coefficient
restriction is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
  [SmoothOfRelativeDimension 0 g]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} (pullback g f))]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} (pullback g f))]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')] in
/-- Original all-degree base change for smooth morphisms of relative dimension zero. -/
theorem higherBaseChangeMap_smoothOfRelativeDimension_zero_isIso (q : ℕ) :
    IsIso (higherBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition q) := by
  let : Etale g := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero g).mpr
    inferInstance
  exact higherBaseChangeMap_etale_isIso f g q

/-- Original bounded-below base change for smooth morphisms of relative dimension zero. -/
theorem derivedBaseChangeMap_smoothOfRelativeDimension_zero_isIso :
    IsIso (derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition) := by
  let : Etale g := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero g).mpr
    inferInstance
  exact derivedBaseChangeMap_etale_isIso f g

end AlgebraicGeometry.Scheme.EtaleCohomology
