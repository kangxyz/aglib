/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineFunctor

/-! # Composition -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- The composition law with named maps and their actual constructor equations.
Only these three equations are transported; the composition backend is unchanged. -/
theorem affineFunctorMap_comp_of_eq
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (L₀ : C₀ ⥤ D₀) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
    (S : C₀ ⥤ C₁) (T : C₁ ⥤ C₂) (ST : C₀ ⥤ C₂)
    (A : D₀ ⥤ D₁) (B : D₁ ⥤ D₂) (AB AB' : D₀ ⥤ D₂)
    (α : L₀ ⋙ A ⟶ S ⋙ L₁) (β : L₁ ⋙ B ⟶ T ⋙ L₂)
    (γ : L₀ ⋙ AB ⟶ ST ⋙ L₂)
    (δ : AB ⟶ AB') (δ' : AB' ⟶ A ⋙ B) (ε : ST ⟶ S ⋙ T)
    {P : C₀} {Q : C₁} {H : C₂} {E : D₀} {F : D₁} {G : D₂}
    (e : L₀.obj P ≅ E) (d : L₁.obj Q ≅ F) (k : L₂.obj H ⟶ G)
    (x : S.obj P ⟶ Q) (y : T.obj Q ⟶ H)
    (hc : δ.app (L₀.obj P) ≫ δ'.app (L₀.obj P) ≫
        B.map (α.app P) ≫ β.app (S.obj P) = γ.app P ≫ L₂.map (ε.app P))
    (a : A.obj E ⟶ F) (b : B.obj F ⟶ G) (c : AB.obj E ⟶ G)
    (ha : a = affineFunctorMap L₀ L₁ S A α e d.hom x)
    (hb : b = affineFunctorMap L₁ L₂ T B β d k y)
    (hcMap : c = affineFunctorMap L₀ L₂ ST AB γ e k (ε.app P ≫ T.map x ≫ y)) :
    δ.app E ≫ δ'.app E ≫ B.map a ≫ b = c := by
  rw [ha, hb, hcMap]
  exact affineFunctorMap_comp L₀ L₁ L₂ S T ST A B AB AB' α β γ δ δ' ε e d k x y hc

end AlgebraicGeometry.Scheme.Modules.Nonflat
