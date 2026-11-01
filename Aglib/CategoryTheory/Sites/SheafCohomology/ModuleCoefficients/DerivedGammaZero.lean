/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGamma
public import Aglib.Algebra.Homology.RightDerived.Zero

/-!
# Degree-zero normalization of actual derived sections

The comparisons retain the original unit into degree-zero right-derived functors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

/-- Deriving a natural transformation preserves the original degree-zero unit. -/
@[reassoc]
lemma toRightDerivedZero_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : C) :
    F.toRightDerivedZero.app X ≫ (NatTrans.rightDerived α 0).app X =
      α.app X ≫ G.toRightDerivedZero.app X :=
  CategoryTheory.Functor.toRightDerivedZero_naturality α X

/-- Exact postcomposition retains the original degree-zero derived-functor unit. -/
@[reassoc]
lemma toRightDerivedZero_postcomp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (X : C) :
    (F ⋙ G).toRightDerivedZero.app X ≫ (rightDerivedPostcompIso F G 0).hom.app X =
      G.map (F.toRightDerivedZero.app X) :=
  CategoryTheory.Functor.toRightDerivedZero_postcomp F G X

end CategoryTheory.Sheaf.ModuleCoefficients
