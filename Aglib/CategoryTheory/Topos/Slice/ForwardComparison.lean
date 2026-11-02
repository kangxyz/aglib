/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # Forward comparison through the original slice equivalences

Native inverse-composition constructors transport the given inverse comparison.
The value theorem retains its original unit/counit chain at the same equivalences.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Equivalence

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) (P : D₁ ⥤ D₂) (Q : C₁ ⥤ C₂)

/-- Transport the actual inverse comparison using the two native constructors. -/
def forwardComparison (α : P ⋙ E₂.inverse ≅ E₁.inverse ⋙ Q) :
    E₁.functor ⋙ P ≅ Q ⋙ E₂.functor :=
  Iso.isoCompInverse (H := E₂.symm)
    (Functor.associator _ _ _ ≪≫ Iso.inverseCompIso (G := E₁.symm) α)

/-- The forward comparison has exactly the original unit/counit factors. -/
theorem forwardComparison_eq_original (α : P ⋙ E₂.inverse ≅ E₁.inverse ⋙ Q) :
    forwardComparison E₁ E₂ P Q α =
      (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft _ E₂.counitIso.symm ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight α _) ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E₁.unitIso.symm _ ≪≫
        Functor.leftUnitor _ := by
  apply Iso.ext
  ext X
  simp [forwardComparison, Iso.isoCompInverse, Iso.inverseCompIso]

end CategoryTheory.Equivalence
