/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Homology
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective module sheaves as module presheaves

The native forgetful functor which forgets the sheaf condition preserves
injectives, because its original left adjoint is exact sheafification.
This does not assert injectivity after forgetting the scalar action.
Ring, module, site and morphism universes remain independent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe r m c h

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- An injective module sheaf is injective as an original module presheaf. -/
instance forget_preservesInjectiveObjects :
    (SheafOfModules.forget.{m} R).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafificationForgetAdjunction R)

end SheafOfModules

namespace CategoryTheory

universe m c h

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{m}]

/-- Forgetting only the sheaf condition preserves injective abelian sheaves. -/
theorem sheafToPresheaf_preservesInjectiveObjects :
    (sheafToPresheaf J AddCommGrpCat.{m}).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafificationAdjunction J AddCommGrpCat.{m})

end CategoryTheory
