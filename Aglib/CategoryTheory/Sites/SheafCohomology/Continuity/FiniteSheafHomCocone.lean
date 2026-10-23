/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFreeHomCocone

/-! # Specified sheaf section cocones and original family cochains

This fixed-site interface keeps the complete native sheaf cochain functor
visible before specializing to a concrete geometric cocone. Its hypotheses
concern only the original tuple section cocones, not the entire sheaf cocone.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.Presheaf.Cech

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe u v uI vI

variable {C : Type u} [Category.{v} C] {K : GrothendieckTopology C}
  {I : Type uI} [Category.{vI} I]
  [HasColimitsOfShape I AddCommGrpCat.{max u v}]
  {W : C} [HasFiniteProducts (Over W)]
  {ι : Type (max u v)} [Finite ι] (U : ι → Over W)
  {D : I ⥤ Sheaf K AddCommGrpCat.{max u v}} (c : Cocone D)

/-- The whole original sheaf cochain cocone is colimiting once its actual tuple
section cocones are colimiting. No global sheaf colimit is used. -/
def finiteFamilySheafHomComplexIsColimit
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsColimit
      (((sheafSections K AddCommGrpCat.{max u v}).obj
        (op (∏ᶜ fun k => U (a k)).left)).mapCocone c)) :
    IsColimit ((sheafToPresheaf K AddCommGrpCat.{max u v} ⋙
      additiveHomFunctor (freeComplex (familyMap U))).mapCocone c) :=
  finiteFamilyHomComplexIsColimit U
    ((sheafToPresheaf K AddCommGrpCat.{max u v}).mapCocone c) hsec

end CategoryTheory.Sheaf.ModuleCoefficients
