/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.Compactness

/-! # Original finite-stage factorization from an actual finite presentation

The input is a real finite presentation by scalar quotients of the genuine
integer free representables, together with real evaluation continuity.
The output factors the original morphism through the original colimit cocone.
No constructibility or geometric continuity assertion is supplied here.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.TorsionFinitePresentation

universe k t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- A finite presentation gives a stage factorization of the literal original morphism. -/
theorem exists_factor_of_finiteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → C) (U1 : Fin r1 → C)
    (h0 : ∀ i, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U0 i)))
    (h1 : ∀ j, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U1 j)))
    {F : Sheaf J AddCommGrpCat.{max v t}}
    (d : finiteFreeZMod.{t} J n U1 ⟶ finiteFreeZMod.{t} J n U0)
    (q : finiteFreeZMod.{t} J n U0 ⟶ F) (hdq : d ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hdq))
    {I : Type k} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf J AddCommGrpCat.{max v t}} {c : Cocone D} (hc : IsColimit c)
    (a : F ⟶ c.pt) : ∃ i, ∃ b : F ⟶ D.obj i, b ≫ c.ι.app i = a := by
  have : IsFinitelyPresentable.{k} F :=
    isFinitelyPresentable_of_finiteZModPresentation J n U0 U1 h0 h1 d q hdq hq
  exact IsFinitelyPresentable.exists_hom_of_isColimit hc a

/-- The original Hom functor sends the actual filtered cocone to a colimit cocone. -/
def homCoconeIsColimitOfFiniteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → C) (U1 : Fin r1 → C)
    (h0 : ∀ i, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U0 i)))
    (h1 : ∀ j, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U1 j)))
    {F : Sheaf J AddCommGrpCat.{max v t}}
    (d : finiteFreeZMod.{t} J n U1 ⟶ finiteFreeZMod.{t} J n U0)
    (q : finiteFreeZMod.{t} J n U0 ⟶ F) (hdq : d ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hdq))
    {I : Type k} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf J AddCommGrpCat.{max v t}} {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op F)).mapCocone c) := by
  have : IsFinitelyPresentable.{k} F :=
    isFinitelyPresentable_of_finiteZModPresentation J n U0 U1 h0 h1 d q hdq hq
  exact isColimitOfPreserves (coyoneda.obj (op F)) hc

end CategoryTheory.Sheaf.TorsionFinitePresentation
