/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Maps carried by a square of functors

A map between two presentations transports through a natural transformation.
The shared constructor makes its composition law available without unfolding
the functors or the presented objects.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- A map between presented objects, transported through a square of functors. -/
def affineFunctorMap
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (L₀ : C₀ ⥤ D₀) (L₁ : C₁ ⥤ D₁) (S : C₀ ⥤ C₁) (A : D₀ ⥤ D₁)
    (α : L₀ ⋙ A ⟶ S ⋙ L₁)
    {P : C₀} {Q : C₁} {E : D₀} {F : D₁}
    (e : L₀.obj P ≅ E) (d : L₁.obj Q ⟶ F) (t : S.obj P ⟶ Q) : A.obj E ⟶ F :=
  A.map e.inv ≫ α.app P ≫ L₁.map t ≫ d

/-- Transported maps compose through the original two comparison transformations.
The intermediate presentation is canceled by its actual inverse. -/
theorem affineFunctorMap_comp
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
        B.map (α.app P) ≫ β.app (S.obj P) = γ.app P ≫ L₂.map (ε.app P)) :
    δ.app E ≫ δ'.app E ≫
        B.map (affineFunctorMap L₀ L₁ S A α e d.hom x) ≫
        affineFunctorMap L₁ L₂ T B β d k y =
      affineFunctorMap L₀ L₂ ST AB γ e k (ε.app P ≫ T.map x ≫ y) := by
  have he := δ.naturality e.inv
  have he' := δ'.naturality e.inv
  change AB'.map e.inv ≫ δ'.app (L₀.obj P) =
    δ'.app E ≫ B.map (A.map e.inv) at he'
  have hx := β.naturality x
  change B.map (L₁.map x) ≫ β.app Q =
    β.app (S.obj P) ≫ L₂.map (T.map x) at hx
  have hd : B.map d.hom ≫ B.map d.inv = 𝟙 _ := by
    rw [← B.map_comp, d.hom_inv_id]
    exact B.map_id _
  simp only [affineFunctorMap, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd, ← reassoc_of% he', ← reassoc_of% he,
    reassoc_of% hx, reassoc_of% hc]

end AlgebraicGeometry.Scheme.Modules.Nonflat
