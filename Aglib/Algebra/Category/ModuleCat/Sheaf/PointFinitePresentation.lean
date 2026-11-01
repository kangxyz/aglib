/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FilteredColimitFinitePresentation
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Finitely presented maps into the native fibre of a module presheaf

The general filtered-colimit factorization applies to the original pointed
neighborhood category. Its conclusion uses the original germ map, without
choosing another stalk model or requiring a constant target presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Presheaf

universe u v r w s

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type r} [Ring R]

/-- A linear map from a finitely presented module into a point fibre lifts to
sections on an actual pointed neighborhood, with the original germ equation. -/
theorem exists_toPresheafFiber_factor_of_finitePresentation
    (Φ : GrothendieckTopology.Point.{s} J)
    [LocallySmall.{s} C] [HasColimitsOfSize.{s, s} (ModuleCat.{w} R)]
    [PreservesFilteredColimitsOfSize.{s, s} (forget (ModuleCat.{w} R))]
    (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (M : ModuleCat.{w} R)
    [Module.FinitePresentation R M] (a : M ⟶ Φ.presheafFiber.obj F) :
    ∃ (U : C) (x : Φ.fiber.obj U) (b : M ⟶ F.obj (op U)),
      b ≫ Φ.toPresheafFiber U x F = a := by
  obtain ⟨i, b, hb⟩ := ModuleCat.exists_factor_of_finitePresentation
    ((Functor.Elements.π Φ.fiber).op ⋙ F) (Φ.presheafFiberCocone F)
    (Φ.isColimitPresheafFiberCocone F) M a
  exact ⟨i.unop.1, i.unop.2, b, hb⟩

end ModuleCat.Presheaf
