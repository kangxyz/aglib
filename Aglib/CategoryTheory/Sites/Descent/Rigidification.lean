/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Transfer

/-!
# Rigidifications along a transformation of pseudofunctors

Let `η : CompTrans F₁ F₂` be a transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
(`Transfer.lean`), and let `E Y` be objects of `F₂` over every `Y : C` with morphisms
`e y : y^* (E V) ⟶ E Y` for `y : Y ⟶ V`. A *rigidification* of `M` over `V` is a morphism
`α : η_V M ⟶ E V`; along `y : Y ⟶ V` it induces the rigidification
`CompTrans.pullRig η E e y α : η_Y (y^* M) ≅ y^* (η_V M) ⟶ y^* (E V) ⟶ E Y` of `y^* M`.

* `CompTrans.pullRig_comp`: if the `e y` are compatible with the composition isomorphisms of
  `F₂`, the rigidification along `g ≫ y` is that along `g` of the rigidification along `y`,
  through the composition isomorphism of `F₁` and `nat_comp`.
* `CompEq`: the equation `f ≫ g = h` as a definition; `CompEq.eq`.
* `CompTrans.RigCompat`, `CompTrans.rigCompat_pullHom`: a morphism `φ : y₁^* M₁ ⟶ y₂^* M₂`
  compatible with two such rigidifications over `Y` stays compatible after Mathlib's `pullHom`
  along any `g : Y' ⟶ Y`.

All statements keep the composite objects of `mapComp'` inside `pullHom` and `nat_comp`, and the
compatibility is the definition `RigCompat`, an instance of `CompEq`, a regular definition: two of
its instances are compared argument by argument before unfolding. Composites written in different
presentations are expensive to compare directly: `CategoryStruct.comp` has abbreviation
reducibility hints, so the kernel unfolds both composites before comparing their arguments
(measured in the Picard instance: 7 to 16 s of kernel time per declaration, against values below
the 100 ms profiler threshold through `CompEq`). The instance in view is
the pullback of module sheaves along the origin sections of a scheme with a section, whose
rigidified line bundles are those of Kleiman (*The Picard scheme*, arXiv:math/0504020v1, Def. 2.8,
p. 19); see `AlgebraicGeometry/Picard/Comparison/GluingDescent.lean`.
-/

@[expose] public section

noncomputable section

universe v' v u' u

namespace CategoryTheory

/-- The equation `f ≫ g = h`, as a definition. Two instances written in different presentations of
one category (for instance a category `↑(Cat.of D)` and `D`) are then compared through their
arguments: `CategoryStruct.comp` is a projection, which the kernel unfolds before comparing
arguments, and this unfolding reaches the underlying morphisms. -/
def CompEq {D : Type u'} [Category.{v'} D] {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    Prop :=
  f ≫ g = h

/-- Two instances of `CompEq` with the same composite have the same right-hand side. Used to
compare an equation stated in one presentation of a category with one stated in another: the two
`CompEq` instances are compared through their arguments. -/
theorem CompEq.eq {D : Type u'} [Category.{v'} D] {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h₁ h₂ : X ⟶ Z} (e₁ : CompEq f g h₁) (e₂ : CompEq f g h₂) : h₁ = h₂ :=
  e₁.symm.trans e₂

end CategoryTheory

namespace CategoryTheory.Pseudofunctor.CompTrans

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F₁ F₂ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : CompTrans F₁ F₂) (E : ∀ Y : C, F₂.obj (.mk (op Y)))
  (e : ∀ ⦃V Y : C⦄ (y : Y ⟶ V), (F₂.map y.op.toLoc).toFunctor.obj (E V) ⟶ E Y)

/-- The rigidification of a pulled-back object: for `α : η_V M ⟶ E V` and `y : Y ⟶ V`, the
composite `η_Y (y^* M) ≅ y^* (η_V M) ⟶ y^* (E V) ⟶ E Y`. -/
def pullRig {V Y : C} (y : Y ⟶ V) {M : F₁.obj (.mk (op V))} (α : (η.app V).obj M ⟶ E V) :
    (η.app Y).obj ((F₁.map y.op.toLoc).toFunctor.obj M) ⟶ E Y :=
  (η.nat y).hom.app M ≫ (F₂.map y.op.toLoc).toFunctor.map α ≫ e y

/-- Compatibility of `φ : y₁^* M₁ ⟶ y₂^* M₂` with the rigidifications of `α₁` and `α₂` over `Y`:
the equation `η_Y φ ≫ pullRig y₂ α₂ = pullRig y₁ α₁`, through `CompEq`. -/
def RigCompat {V₁ V₂ Y : C} (y₁ : Y ⟶ V₁) (y₂ : Y ⟶ V₂) {M₁ : F₁.obj (.mk (op V₁))}
    {M₂ : F₁.obj (.mk (op V₂))} (α₁ : (η.app V₁).obj M₁ ⟶ E V₁) (α₂ : (η.app V₂).obj M₂ ⟶ E V₂)
    (φ : (F₁.map y₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map y₂.op.toLoc).toFunctor.obj M₂) : Prop :=
  CompEq ((η.app Y).map φ) (η.pullRig E e y₂ α₂) (η.pullRig E e y₁ α₁)

variable {η E e}

/-- The rigidification along a composite `g ≫ y`, through the composition isomorphism of `F₁`,
when the maps `e` are compatible with the composition isomorphisms of `F₂`. -/
theorem pullRig_comp
    (he : ∀ ⦃V Y Y' : C⦄ (y : Y ⟶ V) (g : Y' ⟶ Y),
      (F₂.mapComp' y.op.toLoc g.op.toLoc (g ≫ y).op.toLoc rfl).hom.toNatTrans.app (E V) ≫
        (F₂.map g.op.toLoc).toFunctor.map (e y) ≫ e g = e (g ≫ y))
    {V Y Y' : C} (y : Y ⟶ V) (g : Y' ⟶ Y) {M : F₁.obj (.mk (op V))}
    (α : (η.app V).obj M ⟶ E V) :
    η.pullRig E e (g ≫ y) α =
      (η.app Y').map ((F₁.mapComp' y.op.toLoc g.op.toLoc (g ≫ y).op.toLoc
          rfl).hom.toNatTrans.app M) ≫
        (η.nat g).hom.app ((F₁.map y.op.toLoc).toFunctor.obj M) ≫
        (F₂.map g.op.toLoc).toFunctor.map (η.pullRig E e y α) ≫ e g := by
  have hθ := η.nat_comp y g (g ≫ y) rfl M
  have hn := (F₂.mapComp' y.op.toLoc g.op.toLoc (g ≫ y).op.toLoc
    rfl).hom.toNatTrans.naturality α
  simp only [pullRig, Functor.map_comp, Category.assoc]
  rw [← he y g, reassoc_of% hn, reassoc_of% hθ]
  rfl

/-- **Rigidifications are compatible with `pullHom`.** If `φ : y₁^* M₁ ⟶ y₂^* M₂` is compatible
with the rigidifications of `α₁` and `α₂` over `Y`, so is its pullback along `g : Y' ⟶ Y`. -/
theorem rigCompat_pullHom
    (he : ∀ ⦃V Y Y' : C⦄ (y : Y ⟶ V) (g : Y' ⟶ Y),
      (F₂.mapComp' y.op.toLoc g.op.toLoc (g ≫ y).op.toLoc rfl).hom.toNatTrans.app (E V) ≫
        (F₂.map g.op.toLoc).toFunctor.map (e y) ≫ e g = e (g ≫ y))
    {V₁ V₂ Y Y' : C} {y₁ : Y ⟶ V₁} {y₂ : Y ⟶ V₂} {M₁ : F₁.obj (.mk (op V₁))}
    {M₂ : F₁.obj (.mk (op V₂))} {α₁ : (η.app V₁).obj M₁ ⟶ E V₁}
    {α₂ : (η.app V₂).obj M₂ ⟶ E V₂}
    {φ : (F₁.map y₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map y₂.op.toLoc).toFunctor.obj M₂}
    (hφ : η.RigCompat E e y₁ y₂ α₁ α₂ φ)
    (g : Y' ⟶ Y) (gy₁ : Y' ⟶ V₁) (gy₂ : Y' ⟶ V₂) (h₁ : g ≫ y₁ = gy₁) (h₂ : g ≫ y₂ = gy₂) :
    η.RigCompat E e gy₁ gy₂ α₁ α₂ (pullHom φ g gy₁ gy₂ h₁ h₂) := by
  unfold RigCompat CompEq at hφ ⊢
  subst h₁ h₂
  rw [pullRig_comp he y₂ g α₂, pullRig_comp he y₁ g α₁]
  have hc : (η.app Y').map ((F₁.mapComp' y₂.op.toLoc g.op.toLoc (g ≫ y₂).op.toLoc
      rfl).inv.toNatTrans.app M₂) ≫
        (η.app Y').map ((F₁.mapComp' y₂.op.toLoc g.op.toLoc (g ≫ y₂).op.toLoc
          rfl).hom.toNatTrans.app M₂) = 𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, η.nat_hom_naturality_assoc g φ, ← Functor.map_comp_assoc, hφ]

end CategoryTheory.Pseudofunctor.CompTrans
