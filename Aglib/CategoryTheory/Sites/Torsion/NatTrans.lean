/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Colimit
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! # Natural transformations on internally torsion sheaves

Invertibility on positive annihilator stages implies invertibility on a torsion
sheaf when both functors preserve its actual sequential colimit. The comparison
is the supplied natural transformation throughout.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w uD vD

/-- A colimit-preserving comparison invertible on all positive killed sheaves
is invertible on every internally torsion sheaf. -/
theorem natTrans_isIso_of_isTorsion
    {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasColimitsOfShape ℕ D]
    (L R : Sheaf J AddCommGrpCat.{w} ⥤ D) (α : L ⟶ R)
    [PreservesColimitsOfShape ℕ L] [PreservesColimitsOfShape ℕ R]
    (hbounded : ∀ (n : ℕ), n ≠ 0 →
      ∀ F : Sheaf J AddCommGrpCat.{w}, n • 𝟙 F = 0 → IsIso (α.app F))
    (F : Sheaf J AddCommGrpCat.{w}) (hF : Sheaf.IsTorsion F) : IsIso (α.app F) := by
  let K := Sheaf.factorialAnnihilatorDiagram F
  let (i : ℕ) : IsIso ((Functor.whiskerLeft K α).app i) :=
    hbounded (i + 1).factorial
      (ne_of_gt (Sheaf.factorialAnnihilatorDiagram_exponent_pos i))
      (K.obj i) (Sheaf.factorialAnnihilatorDiagram_annihilated F i)
  let : IsIso (Functor.whiskerLeft K α) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft K α)
  exact isIso_app_coconePt_of_preservesColimit K α
    (Sheaf.factorialAnnihilatorCocone F) (Sheaf.factorialAnnihilatorCoconeIsColimit F hF)

end CategoryTheory.Sheaf
