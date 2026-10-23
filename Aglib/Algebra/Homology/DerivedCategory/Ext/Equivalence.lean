/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Original Ext comparison through an additive equivalence

An actual additive equivalence and a source isomorphism make the existing
exact-functor/source-precomposition map bijective. The Ext universes remain
independent; no replacement Ext groups are defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- The literal Ext map of an equivalence, followed by source-isomorphism
precomposition, is bijective in every degree. -/
theorem extPrecompMap_bijective_of_isEquivalence
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] [EnoughInjectives C]
    {X : C} {A : D} (a : A ⟶ F.obj X) [IsIso a] (Y : C) (n : ℕ) :
    Function.Bijective (F.extPrecompMap a Y n) := by
  let e := (((extFunctor n).mapIso (asIso a).op).app (F.obj Y)).addCommGroupIsoToAddEquiv
  exact e.bijective.comp (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)

end CategoryTheory.Functor
