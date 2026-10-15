/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Bounded-below derived direct image of module sheaves

The installed right-derived functor retains its actual derived unit. Module sheaves
have enough injectives, so this construction needs no geometric hypothesis on
the morphism. Preservation of perfect objects requires a separate proof.
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedPushforwardPlus.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 39]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard ambient derived category of actual module sheaves. -/
local instance derivedPushforwardPlusStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The actual right-derived direct image on bounded-below derived categories. -/
def derivedPushforwardPlus {Z X : Scheme.{u}} (f : Z ⟶ X) :
    DerivedCategory.Plus Z.Modules ⥤ DerivedCategory.Plus X.Modules :=
  (Scheme.Modules.pushforward f).rightDerivedFunctorPlus

/-- The original unit from termwise direct image to its bounded-below right-derived functor. -/
def derivedPushforwardPlusUnit {Z X : Scheme.{u}} (f : Z ⟶ X) :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit

end AlgebraicGeometry.Scheme.Modules
