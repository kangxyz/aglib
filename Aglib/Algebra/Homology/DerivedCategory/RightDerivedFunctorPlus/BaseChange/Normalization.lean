/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Naturality of the native mate under comparison maps

Top and bottom comparison transformations normalize horizontal pasting and identity squares.
The square compatibility is explicit; unrelated comparison isomorphisms are not identified.
-/

@[expose] public section

namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G G' : C ⥤ E} {H H' : D ⥤ F}

/-- Naturality of native mates with respect to the top and bottom functors. -/
theorem mateEquiv_top_bottom_naturality (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁ L₂ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ X, L₂.map (γ.app X) ≫ α'.app X = α.app X ≫ δ.app (L₁.obj X))
    (K : D) :
    γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α').app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj₂.counit.naturality (δ.app K)
  change L₂.map (R₂.map (δ.app K)) ≫ adj₂.counit.app (H'.obj K) =
    adj₂.counit.app (H.obj K) ≫ δ.app K at hn
  rw [hn, reassoc_of% (mateEquiv_counit adj₁ adj₂ α K),
    mateEquiv_counit adj₁ adj₂ α' K]
  rw [← Category.assoc, h, Category.assoc, ← δ.naturality]
  rfl

end CategoryTheory
