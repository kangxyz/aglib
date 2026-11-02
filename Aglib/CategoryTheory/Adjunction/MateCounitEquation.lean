/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The original counit face of a specified mixed mate

The predicate keeps the supplied transformation explicit. Concrete consumers
can carry the entire face without expanding large native adjunction terms.
-/

@[expose] public section
namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The counit face retains both original adjunctions and the actual mixed map. -/
def SpecifiedMateCounitEquation (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (σ : R₁ ⋙ G ⟶ H ⋙ R₂) : Prop :=
  ∀ K, L₂.map (σ.app K) ≫ a₂.counit.app (H.obj K) =
    α.app (R₁.obj K) ≫ H.map (a₁.counit.app K)

/-- The native mixed mate satisfies its original counit face. -/
theorem specifiedMateCounitEquation (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) :
    SpecifiedMateCounitEquation a₁ a₂ α (mateEquiv a₁ a₂ α).natTrans :=
  fun K => mateEquiv_counit a₁ a₂ α K

end CategoryTheory
