/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Exact open restriction in the bounded-below derived category

Source:
`Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedOpenBaseChange.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`f8885ace11ed0ee182729887d1c57ccdcf7f094cc9a3d47fa53aa3c1bf1860f9`.
Selected declarations: derivedRestrictionPlus, isIso_derivedRestrictionPlusUnit.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category model for module sheaves on `X` in open-restriction
comparisons. -/
local instance restrictionPlusDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The bounded-below right derived restriction functor along the open immersion `j`. -/
def derivedRestrictionPlus {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus U.Modules :=
  (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus

theorem isIso_derivedRestrictionPlusUnit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusUnit :=
  (Scheme.Modules.restrictFunctor j).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology

end AlgebraicGeometry.Scheme.Modules
