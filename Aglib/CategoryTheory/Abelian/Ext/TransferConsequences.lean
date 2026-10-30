/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Equivalence

/-! # Actual exact transfer and invertible original comparisons

The original exact-functor/source map and original coefficient isomorphism
construct the same transfer. Bijectivity follows from the actual equivalence
and source comparison; no replacement Ext theory or arbitrary endpoint map is
introduced. Category, morphism and Ext worlds remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe uC vC uD vD eC eD

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]

/-- The actual equivalence and original source/coefficient isomorphisms give bijective transfer. -/
theorem extCoefficientTransfer_bijective_of_isEquivalence
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] [EnoughInjectives C]
    {U : C} {V : D} (s : V ⟶ F.obj U) [IsIso s]
    {X : C} {Y : D} (e : F.obj X ≅ Y) (n : ℕ) :
    Function.Bijective (F.extCoefficientTransfer s e.hom n) :=
  (((extFunctorObj V n).mapIso e).addCommGroupIsoToAddEquiv.bijective).comp
    (F.extPrecompMap_bijective_of_isEquivalence s X n)

end CategoryTheory.Functor
