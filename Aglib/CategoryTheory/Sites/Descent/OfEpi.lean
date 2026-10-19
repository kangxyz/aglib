/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Bind

/-!
# Descent data on quotients of a descent datum

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, `D` a descent datum for a family
`f i : X i ⟶ S`, and `p i : D.obj i ⟶ obj i` morphisms that remain epimorphisms after every
pullback `F.map g`. Morphisms `hom` between the pullbacks of the `obj i` that are compatible with
`p` and with `D.hom` form a descent datum `DescentData.ofEpi D obj p hp hom hhom`, and the `p i`
form a morphism of descent data `toOfEpi : D ⟶ ofEpi …`. The three axioms of a descent datum
(compatibility with pullback, `hom_self`, `hom_comp`) hold because they hold for `D` and every
equation can be checked after the epimorphisms `p`. `LocallyDiscreteOpToCat.pullHom_map` computes
`pullHom` of the image of a morphism under `F.map f₁`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v v' u'

open CategoryTheory Opposite Limits

namespace CategoryTheory.Pseudofunctor

open Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

/-- `pullHom` of the image of a morphism under `F.map f₁` is its image under `F.map gf₁`. -/
lemma pullHom_map ⦃X₁ : C⦄ ⦃M M' : F.obj (.mk (op X₁))⦄ (ψ : M ⟶ M') ⦃Y : C⦄ (f₁ : Y ⟶ X₁)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map ψ) g gf₁ gf₁ hgf₁ hgf₁ =
      (F.map gf₁.op.toLoc).toFunctor.map ψ := by
  simp [pullHom]

end LocallyDiscreteOpToCat

namespace DescentData

variable {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- **Descent data of quotients.** Let `D` be a descent datum and `p i : D.obj i ⟶ obj i`
morphisms that stay epimorphisms after every pullback. Morphisms `hom` compatible with `p` and
with `D.hom` form a descent datum on `obj`. -/
def ofEpi (D : F.DescentData f) (obj : ∀ i, F.obj (.mk (op (X i))))
    (p : ∀ i, D.obj i ⟶ obj i)
    (hp : ∀ ⦃Y : C⦄ (i : ι) (g : Y ⟶ X i), Epi ((F.map g.op.toLoc).toFunctor.map (p i)))
    (hom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂),
      f₁ ≫ f i₁ = q → f₂ ≫ f i₂ = q →
        ((F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)))
    (hhom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (p i₁) ≫ hom q f₁ f₂ hf₁ hf₂ =
        D.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (p i₂)) :
    F.DescentData f where
  obj := obj
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := hom q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    have := hp i₁ gf₁
    rw [← cancel_epi ((F.map gf₁.op.toLoc).toFunctor.map (p i₁)), hhom q' gf₁ gf₂,
      ← pullHom_map (p i₁) f₁ g gf₁ hgf₁, ← pullHom_comp _ _ g gf₁ gf₁ gf₂ hgf₁ hgf₁ hgf₂, hhom,
      pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂,
      D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂, pullHom_map]
  hom_self Y q i g hg := by
    have := hp i g
    rw [← cancel_epi ((F.map g.op.toLoc).toFunctor.map (p i)), hhom, D.hom_self q g hg,
      Category.id_comp, Category.comp_id]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have := hp i₁ f₁
    rw [← cancel_epi ((F.map f₁.op.toLoc).toFunctor.map (p i₁)), reassoc_of% hhom, hhom,
      ← Category.assoc, D.hom_comp, hhom]

/-- The morphisms `p i` form a morphism of descent data `D ⟶ ofEpi D obj p hp hom hhom`. -/
def toOfEpi (D : F.DescentData f) (obj : ∀ i, F.obj (.mk (op (X i))))
    (p : ∀ i, D.obj i ⟶ obj i)
    (hp : ∀ ⦃Y : C⦄ (i : ι) (g : Y ⟶ X i), Epi ((F.map g.op.toLoc).toFunctor.map (p i)))
    (hom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂),
      f₁ ≫ f i₁ = q → f₂ ≫ f i₂ = q →
        ((F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)))
    (hhom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (p i₁) ≫ hom q f₁ f₂ hf₁ hf₂ =
        D.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (p i₂)) :
    D ⟶ ofEpi D obj p hp hom hhom where
  hom := p
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := hhom q f₁ f₂ hf₁ hf₂

end DescentData

end CategoryTheory.Pseudofunctor
