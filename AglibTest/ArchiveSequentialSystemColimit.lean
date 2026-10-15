/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.EventuallyIsoColimit

/-! Original colimit legs and tail comparisons for an arbitrary category. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.SequentialSystem

universe u v

variable {C : Type u} [Category.{v} C]

example (F : ℕ ⥤ C) [HasColimit F] (i : ℕ)
    (h : ∀ n, i ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) :
    IsIso (colimit.ι F i) :=
  colimit_ι_isIso_of_tail F i h

example (F : ℕ ⥤ C) [HasColimit F]
    [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))] :
    colimit.ι F 0 = (colimitIsoOfSucc F).inv :=
  colimit_ι_zero_eq_inv F

example (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι (shiftFunctor t ⋙ F) n ≫ (tailColimitIso F t).hom =
      colimit.ι F (t + n) :=
  tailColimitIso_ι_hom F t n

example (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι F (t + n) ≫ (tailColimitIso F t).inv =
      colimit.ι (shiftFunctor t ⋙ F) n :=
  tailColimitIso_ι_inv F t n

example (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) {X : C}
    (f : colimit F ⟶ X) :
    colimit.ι (shiftFunctor t ⋙ F) n ≫ (tailColimitIso F t).hom ≫ f =
      colimit.ι F (t + n) ≫ f :=
  tailColimitIso_ι_hom_assoc F t n f

example (F : ℕ ⥤ C) [HasColimit F]
    [∀ n, IsIso (F.map (homOfLE (Nat.le_succ n)))] (n : ℕ) :
    colimit.ι F n ≫ (colimitIsoOfSucc F).hom =
      (toZeroIso (fun n ↦ F.map (homOfLE (Nat.le_succ n))) n).hom :=
  ι_colimitIsoOfSucc_hom F n
