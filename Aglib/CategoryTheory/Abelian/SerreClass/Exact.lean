/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# Exact functors from additive Serre localization

An additive Serre localization is bundled as the selected exact functor between the standard
abelian exact structures, retaining independent source and target universes.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Localization/Serre/Localization.lean`.
SHA-256: `f9f34ad188f0a6422b598b35b49d2c911dcd3dee87202ccefc8623f96ed95b40`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- An additive Serre localization is an exact functor for the standard exact
structures. Finite limit and colimit preservation are proved by mathlib from
the Serre localization hypotheses. -/
def serreLocalization : ExactFunctor (abelianExactStructure C) (abelianExactStructure D) where
  toFunctor := L
  map_conflation S hS := by
    let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
    exact hS.map_of_exact L

end CategoryTheory.ExactCategory.ExactFunctor
