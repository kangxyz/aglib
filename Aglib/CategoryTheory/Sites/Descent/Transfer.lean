/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Transfer of descent data along a transformation of pseudofunctors

Let `F₁ F₂ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. A `Pseudofunctor.CompTrans F₁ F₂` consists of functors
`app X : F₁.obj ⟨op X⟩ ⥤ F₂.obj ⟨op X⟩`, natural isomorphisms
`nat f : F₁.map f ⋙ app Y ≅ app X ⋙ F₂.map f` for `f : Y ⟶ X`, and the compatibility of `nat`
with the composition isomorphisms `mapComp'` of the two pseudofunctors (`nat_comp`). These are
the components, pseudonaturality isomorphisms and composition coherence of a strong transformation
`F₁ ⟶ F₂` (Mathlib's `Pseudofunctor.StrongTrans`), stated componentwise; the unit coherence is
omitted because the transfer of descent data does not use it.

Such a transformation `η` induces a functor `η.descentData f : F₁.DescentData f ⥤ F₂.DescentData f`
for every family `f i : X i ⟶ S` (objects go through `app`, descent morphisms are conjugated by
`nat`, `CompTrans.conj`), compatible with `toDescentData` (`CompTrans.toDescentDataIso`). The key
computation is `CompTrans.pullHom_conj`: conjugation commutes with Mathlib's `pullHom`. If every
`app X` is an equivalence, then `η.descentData f` is an equivalence, and `F₂.IsStackFor R` follows
from `F₁.IsStackFor R` (`CompTrans.isStackFor_of_isStackFor`).

The file also provides `Pseudofunctor.DescentData.transport`, the transport of a descent datum along
isomorphisms of its objects, and `LocallyDiscreteOpToCat.pullHom_map_comp_comp_map`, the behaviour
of `pullHom` on a morphism framed by images of morphisms.
-/

@[expose] public section

noncomputable section

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]

namespace LocallyDiscreteOpToCat

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

-- As for Mathlib's `pullHom`: the objects of `F.obj _` (a `Cat.of`) must be seen as objects of the
-- underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism framed by the images of morphisms `a` and `b`. -/
@[reassoc]
lemma pullHom_map_comp_comp_map ⦃X₁ X₂ : C⦄ ⦃M₁ M₁' : F.obj (.mk (op X₁))⦄
    ⦃M₂ M₂' : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (a : M₁ ⟶ M₁')
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : M₂ ⟶ M₂') ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map a ≫ h ≫ (F.map f₂.op.toLoc).toFunctor.map b)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (F.map gf₁.op.toLoc).toFunctor.map a ≫ pullHom h g gf₁ gf₂ hgf₁ hgf₂ ≫
        (F.map gf₂.op.toLoc).toFunctor.map b := by
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [← mapComp'_hom_naturality_assoc, mapComp'_inv_naturality]

end LocallyDiscreteOpToCat

namespace DescentData

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {ι : Type t} {S : C} {X : ι → C}
  {f : ∀ i, X i ⟶ S}

/-- The transport of a descent datum along isomorphisms `e i : N i ≅ D.obj i`. -/
@[simps]
def transport (D : F.DescentData f) {N : ∀ i, F.obj (.mk (op (X i)))}
    (e : ∀ i, N i ≅ D.obj i) : F.DescentData f where
  obj := N
  hom _ q _ _ f₁ f₂ hf₁ hf₂ :=
    (F.map f₁.op.toLoc).toFunctor.map (e _).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map (e _).inv
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullHom_map_comp_comp_map, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self _ q _ g hg := by
    rw [D.hom_self q g hg, Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
      D.hom_comp_assoc q f₁ f₂ f₃ hf₁ hf₂ hf₃]

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- The transported datum is isomorphic to the original one. -/
@[simps!]
def transportIso (D : F.DescentData f) {N : ∀ i, F.obj (.mk (op (X i)))}
    (e : ∀ i, N i ≅ D.obj i) : D.transport e ≅ D :=
  isoMk e (fun _ _ _ _ _ _ _ _ ↦ by simp)

end DescentData

variable (F₁ F₂ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A transformation `F₁ ⟶ F₂` of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`: functors `app X`,
pseudonaturality isomorphisms `nat f` and their compatibility with the composition isomorphisms
`mapComp'` (`nat_comp`, stated componentwise). These are the data and the composition coherence of
a strong transformation; the unit coherence is not needed for descent data and is omitted. -/
structure CompTrans where
  /-- The functor over `X`. -/
  app (X : C) : F₁.obj (.mk (op X)) ⥤ F₂.obj (.mk (op X))
  /-- The pseudonaturality isomorphism along `f : Y ⟶ X`. -/
  nat {X Y : C} (f : Y ⟶ X) :
    (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅ app X ⋙ (F₂.map f.op.toLoc).toFunctor
  /-- Compatibility with the composition isomorphisms. -/
  nat_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
      (M : F₁.obj (.mk (op X))) :
    (nat gf).hom.app M ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((app X).obj M) =
      (app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
        (nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (F₂.map g.op.toLoc).toFunctor.map ((nat f).hom.app M)

namespace CompTrans

variable {F₁ F₂} (η : CompTrans F₁ F₂)

attribute [reassoc] nat_comp

@[reassoc]
lemma nat_hom_naturality {X Y : C} (f : Y ⟶ X) {M M' : F₁.obj (.mk (op X))} (a : M ⟶ M') :
    (η.app Y).map ((F₁.map f.op.toLoc).toFunctor.map a) ≫ (η.nat f).hom.app M' =
      (η.nat f).hom.app M ≫ (F₂.map f.op.toLoc).toFunctor.map ((η.app X).map a) :=
  (η.nat f).hom.naturality a

@[reassoc]
lemma nat_inv_naturality {X Y : C} (f : Y ⟶ X) {M M' : F₁.obj (.mk (op X))} (a : M ⟶ M') :
    (F₂.map f.op.toLoc).toFunctor.map ((η.app X).map a) ≫ (η.nat f).inv.app M' =
      (η.nat f).inv.app M ≫ (η.app Y).map ((F₁.map f.op.toLoc).toFunctor.map a) :=
  (η.nat f).inv.naturality a

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- `nat_comp`, solved for the inverse of `nat f`. -/
@[reassoc]
lemma mapComp'_hom_app_comp_map_nat_inv_app {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F₁.obj (.mk (op X))) :
    (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
        ((η.app X).obj M) ≫ (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).inv.app M) =
      (η.nat gf).inv.app M ≫
        (η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
        (η.nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) := by
  have hN := η.nat_comp f g gf h M
  calc _ = ((η.nat gf).inv.app M ≫ (η.nat gf).hom.app M) ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((η.app X).obj M) ≫ (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).inv.app M) := by
        rw [Iso.inv_hom_id_app, Category.id_comp]
    _ = (η.nat gf).inv.app M ≫ ((η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
        (η.nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).hom.app M)) ≫
          (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).inv.app M) := by
        rw [Category.assoc, ← Category.assoc ((η.nat gf).hom.app M), hN]
    _ = _ := by
        simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
          Functor.map_id, Category.comp_id]

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- `nat_comp`, solved for the inverse of `mapComp'`. -/
@[reassoc]
lemma map_nat_hom_app_comp_mapComp'_inv_app {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F₁.obj (.mk (op X))) :
    (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).hom.app M) ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((η.app X).obj M) =
      (η.nat g).inv.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).inv.toNatTrans.app M) ≫
        (η.nat gf).hom.app M := by
  have hN := η.nat_comp f g gf h M
  calc _ = ((η.nat g).inv.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).inv.toNatTrans.app M)) ≫
        ((η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
        (η.nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (F₂.map g.op.toLoc).toFunctor.map ((η.nat f).hom.app M)) ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((η.app X).obj M) := by
        simp only [Functor.comp_obj, Cat.Hom.comp_toFunctor, Category.assoc,
          ← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id,
          Category.id_comp, Iso.inv_hom_id_app_assoc]
    _ = ((η.nat g).inv.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (η.app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).inv.toNatTrans.app M)) ≫
        ((η.nat gf).hom.app M ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((η.app X).obj M)) ≫
        (F₂.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((η.app X).obj M) := by
        rw [hN]
    _ = _ := by
        simp only [Functor.comp_obj, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
          Category.comp_id]

section conj

variable ⦃X₁ X₂ : C⦄ ⦃M₁ : F₁.obj (.mk (op X₁))⦄ ⦃M₂ : F₁.obj (.mk (op X₂))⦄
  ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄

/-- Conjugation by the pseudonaturality isomorphisms: a morphism
`f₁^* M₁ ⟶ f₂^* M₂` for `F₁` gives a morphism `f₁^* (app X₁ M₁) ⟶ f₂^* (app X₂ M₂)` for `F₂`. -/
def conj (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂) :
    (F₂.map f₁.op.toLoc).toFunctor.obj ((η.app X₁).obj M₁) ⟶
      (F₂.map f₂.op.toLoc).toFunctor.obj ((η.app X₂).obj M₂) :=
  (η.nat f₁).inv.app M₁ ≫ (η.app Y).map h ≫ (η.nat f₂).hom.app M₂

@[simp]
lemma conj_id ⦃X : C⦄ ⦃M : F₁.obj (.mk (op X))⦄ ⦃f : Y ⟶ X⦄ :
    η.conj (𝟙 ((F₁.map f.op.toLoc).toFunctor.obj M)) = 𝟙 _ := by
  simp [conj]

@[reassoc (attr := simp)]
lemma conj_comp ⦃X₃ : C⦄ ⦃M₃ : F₁.obj (.mk (op X₃))⦄ ⦃f₃ : Y ⟶ X₃⦄
    (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂)
    (h' : (F₁.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F₁.map f₃.op.toLoc).toFunctor.obj M₃) :
    η.conj h ≫ η.conj h' = η.conj (h ≫ h') := by
  simp [conj]

/-- Naturality of conjugation in the objects. -/
@[reassoc]
lemma map_comp_conj {M₁' : F₁.obj (.mk (op X₁))} {M₂' : F₁.obj (.mk (op X₂))}
    (a : M₁ ⟶ M₁') (b : M₂ ⟶ M₂')
    (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂)
    (h' : (F₁.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂')
    (w : (F₁.map f₁.op.toLoc).toFunctor.map a ≫ h' = h ≫ (F₁.map f₂.op.toLoc).toFunctor.map b) :
    (F₂.map f₁.op.toLoc).toFunctor.map ((η.app X₁).map a) ≫ η.conj h' =
      η.conj h ≫ (F₂.map f₂.op.toLoc).toFunctor.map ((η.app X₂).map b) := by
  simp only [conj, Category.assoc]
  rw [η.nat_inv_naturality_assoc, ← Functor.map_comp_assoc, w, Functor.map_comp_assoc,
    η.nat_hom_naturality]

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- The converse of `map_comp_conj` when `app Y` is faithful. -/
lemma map_comp_eq_of_map_comp_conj (hY : (η.app Y).Faithful)
    {M₁' : F₁.obj (.mk (op X₁))} {M₂' : F₁.obj (.mk (op X₂))} (a : M₁ ⟶ M₁') (b : M₂ ⟶ M₂')
    (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂)
    (h' : (F₁.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂')
    (w : (F₂.map f₁.op.toLoc).toFunctor.map ((η.app X₁).map a) ≫ η.conj h' =
      η.conj h ≫ (F₂.map f₂.op.toLoc).toFunctor.map ((η.app X₂).map b)) :
    (F₁.map f₁.op.toLoc).toFunctor.map a ≫ h' = h ≫ (F₁.map f₂.op.toLoc).toFunctor.map b := by
  apply hY.map_injective
  simp only [conj, Category.assoc] at w
  rw [η.nat_inv_naturality_assoc, ← Functor.map_comp_assoc, ← η.nat_hom_naturality,
    ← Functor.map_comp_assoc] at w
  exact (cancel_mono _).1 ((cancel_epi _).1 w)

/-- The inverse of conjugation, when `app Y` is fully faithful. -/
def unconj (hY : (η.app Y).FullyFaithful)
    (k : (F₂.map f₁.op.toLoc).toFunctor.obj ((η.app X₁).obj M₁) ⟶
      (F₂.map f₂.op.toLoc).toFunctor.obj ((η.app X₂).obj M₂)) :
    (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂ :=
  hY.preimage ((η.nat f₁).hom.app M₁ ≫ k ≫ (η.nat f₂).inv.app M₂)

@[simp]
lemma conj_unconj (hY : (η.app Y).FullyFaithful)
    (k : (F₂.map f₁.op.toLoc).toFunctor.obj ((η.app X₁).obj M₁) ⟶
      (F₂.map f₂.op.toLoc).toFunctor.obj ((η.app X₂).obj M₂)) :
    η.conj (η.unconj hY k) = k := by
  simp [conj, unconj]

@[simp]
lemma unconj_conj (hY : (η.app Y).FullyFaithful)
    (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂) :
    η.unconj hY (η.conj h) = h := by
  apply hY.map_injective
  simp [conj, unconj]

lemma conj_injective (hY : (η.app Y).FullyFaithful)
    {h h' : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂}
    (e : η.conj h = η.conj h') : h = h' := by
  rw [← η.unconj_conj hY h, e, η.unconj_conj hY h']

-- As for Mathlib's `pullHom`.
set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation commutes with `pullHom`.** -/
lemma pullHom_conj
    (h : (F₁.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F₁.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (η.conj h) g gf₁ gf₂ hgf₁ hgf₂ = η.conj (pullHom h g gf₁ gf₂ hgf₁ hgf₂) := by
  simp only [pullHom, conj, Functor.map_comp, Category.assoc]
  rw [η.mapComp'_hom_app_comp_map_nat_inv_app_assoc f₁ g gf₁ hgf₁ M₁,
    η.map_nat_hom_app_comp_mapComp'_inv_app f₂ g gf₂ hgf₂ M₂, ← η.nat_hom_naturality_assoc,
    Iso.hom_inv_id_app_assoc]

end conj

section descentData

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The descent datum for `F₂` obtained from a descent datum for `F₁` by applying `η`. -/
@[simps]
def descentDataObj (D : F₁.DescentData f) : F₂.DescentData f where
  obj i := (η.app (X i)).obj (D.obj i)
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := η.conj (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [η.pullHom_conj, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self _ q _ g hg := by rw [D.hom_self q g hg, conj_id]
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by rw [conj_comp, D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]

/-- The functor on descent data induced by `η`. -/
@[simps]
def descentData : F₁.DescentData f ⥤ F₂.DescentData f where
  obj D := η.descentDataObj f D
  map {D₁ D₂} φ :=
    { hom i := (η.app (X i)).map (φ.hom i)
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := η.map_comp_conj _ _ _ _ (φ.comm q f₁ f₂ hf₁ hf₂) }

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category, and
-- `dsimp` must use the `simps` lemmas of `descentDataObj` (as in Mathlib's `DescentData.lean`).
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `toDescentData` commutes with `η`. -/
def toDescentDataIso :
    F₁.toDescentData f ⋙ η.descentData f ≅ η.app S ⋙ F₂.toDescentData f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk (fun i ↦ (η.nat (f i)).app M) (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp only [Functor.comp_obj, descentData_obj, descentDataObj_hom, descentDataObj_obj,
        toDescentData_obj, DescentData.ofObj_hom, DescentData.ofObj_obj, Iso.app_hom]
      simp only [conj, Functor.map_comp, Category.assoc]
      rw [η.map_nat_hom_app_comp_mapComp'_inv_app_assoc (f i₁) f₁ q hf₁ M,
        η.nat_comp (f i₂) f₂ q hf₂ M]))
    (fun φ ↦ by
      ext i
      exact η.nat_hom_naturality (f i) φ)

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- `η.descentData f` is fully faithful when the functors `app X` are. -/
def fullyFaithfulDescentData (hη : ∀ X, (η.app X).FullyFaithful) :
    (η.descentData f).FullyFaithful where
  preimage {D₁ D₂} ψ :=
    { hom i := (hη (X i)).preimage (ψ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        refine η.map_comp_eq_of_map_comp_conj (hη Y).faithful _ _ (D₁.hom q f₁ f₂ hf₁ hf₂)
          (D₂.hom q f₁ f₂ hf₁ hf₂) ?_
        rw [(hη (X i₁)).map_preimage, (hη (X i₂)).map_preimage]
        exact ψ.comm q f₁ f₂ hf₁ hf₂ }
  map_preimage {D₁ D₂} ψ := by
    ext i
    exact (hη (X i)).map_preimage (ψ.hom i)
  preimage_map {D₁ D₂} φ := by
    ext i
    exact (hη (X i)).preimage_map (φ.hom i)

-- As for `toDescentDataIso`.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `η.descentData f` is essentially surjective when the functors `app X` are equivalences. -/
lemma essSurj_descentData (hη : ∀ X, (η.app X).FullyFaithful) [∀ X, (η.app X).EssSurj] :
    (η.descentData f).EssSurj where
  mem_essImage D₂ := by
    let e (i : ι) : (η.app (X i)).obj ((η.app (X i)).objPreimage (D₂.obj i)) ≅ D₂.obj i :=
      (η.app (X i)).objObjPreimageIso (D₂.obj i)
    let D₂' := D₂.transport e
    let D₁ : F₁.DescentData f :=
      { obj i := (η.app (X i)).objPreimage (D₂.obj i)
        hom _ q _ _ f₁ f₂ hf₁ hf₂ := η.unconj (hη _) (D₂'.hom q f₁ f₂ hf₁ hf₂)
        pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
          apply η.conj_injective (hη _)
          rw [← η.pullHom_conj, conj_unconj, conj_unconj,
            D₂'.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
        hom_self _ q _ g hg := by
          apply η.conj_injective (hη _)
          rw [conj_unconj, conj_id, D₂'.hom_self q g hg]
          rfl
        hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
          apply η.conj_injective (hη _)
          rw [← conj_comp, conj_unconj, conj_unconj, conj_unconj,
            D₂'.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃] }
    refine ⟨D₁, ⟨DescentData.isoMk e (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ ?_)⟩⟩
    simp only [descentData_obj, descentDataObj_hom, D₁, conj_unconj, D₂', DescentData.transport_hom,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

lemma isEquivalence_descentData [∀ X, (η.app X).IsEquivalence] :
    (η.descentData f).IsEquivalence := by
  have hη : ∀ X, (η.app X).FullyFaithful := fun X ↦ Functor.FullyFaithful.ofFullyFaithful _
  have := (η.fullyFaithfulDescentData f hη).full
  have := (η.fullyFaithfulDescentData f hη).faithful
  have := η.essSurj_descentData f hη
  exact { }

/-- If the functors `app X` are equivalences and `F₁.toDescentData f` is an equivalence, so is
`F₂.toDescentData f`. -/
lemma isEquivalence_toDescentData [∀ X, (η.app X).IsEquivalence]
    [(F₁.toDescentData f).IsEquivalence] : (F₂.toDescentData f).IsEquivalence := by
  have := η.isEquivalence_descentData f
  have : (η.app S ⋙ F₂.toDescentData f).IsEquivalence :=
    Functor.isEquivalence_of_iso (η.toDescentDataIso f)
  exact Functor.isEquivalence_of_comp_left (η.app S) (F₂.toDescentData f)

-- As for `CompTrans.essSurj_descentData`: the objects of `F.obj _` (a `Cat.of`) must be seen as
-- objects of the underlying category, and `dsimp` must use the `simps` lemmas of the descent-data
-- constructions.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Lifting descent data along a transformation, on a class of objects.** Let `P` be a class of
objects stable under the functors `F₁.map g`, such that `η.app Y` is bijective on morphisms with
target in `P`. A descent datum `D₂` for `F₂` whose objects are isomorphic to `η.app (X i)` of
objects `M i` in `P` is the image under `η.descentData f` of a descent datum for `F₁`. -/
theorem exists_descentData_iso_of_bijective
    (P : ∀ ⦃Y : C⦄, F₁.obj (.mk (op Y)) → Prop)
    (hP : ∀ ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (M : F₁.obj (.mk (op Y))), P M →
      P ((F₁.map g.op.toLoc).toFunctor.obj M))
    (hη : ∀ ⦃Y : C⦄ (N N' : F₁.obj (.mk (op Y))), P N' →
      Function.Bijective (fun φ : N ⟶ N' ↦ (η.app Y).map φ))
    (D₂ : F₂.DescentData f) (M : ∀ i, F₁.obj (.mk (op (X i)))) (hM : ∀ i, P (M i))
    (e : ∀ i, (η.app (X i)).obj (M i) ≅ D₂.obj i) :
    ∃ D₁ : F₁.DescentData f, Nonempty ((η.descentData f).obj D₁ ≅ D₂) := by
  let D₂' := D₂.transport e
  have hb : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂),
      Function.Bijective (fun φ : (F₁.map f₁.op.toLoc).toFunctor.obj (M i₁) ⟶
        (F₁.map f₂.op.toLoc).toFunctor.obj (M i₂) ↦ η.conj φ) := by
    intro Y i₁ i₂ f₁ f₂
    have h := hη ((F₁.map f₁.op.toLoc).toFunctor.obj (M i₁))
      ((F₁.map f₂.op.toLoc).toFunctor.obj (M i₂)) (hP f₂ _ (hM i₂))
    refine ⟨fun φ φ' hφ ↦ h.1 ?_, fun k ↦ ?_⟩
    · have hφ' : η.conj φ = η.conj φ' := hφ
      simp only [conj] at hφ'
      exact (cancel_mono _).1 ((cancel_epi _).1 hφ')
    · obtain ⟨φ, hφ⟩ := h.2 ((η.nat f₁).hom.app (M i₁) ≫ k ≫ (η.nat f₂).inv.app (M i₂))
      refine ⟨φ, ?_⟩
      change η.conj φ = k
      simp only [conj]
      change (η.nat f₁).inv.app (M i₁) ≫ (fun φ ↦ (η.app Y).map φ) φ ≫
        (η.nat f₂).hom.app (M i₂) = k
      rw [hφ]
      simp
  have hc : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) k,
      η.conj (Function.surjInv (hb f₁ f₂).2 k) = k :=
    fun _ _ _ f₁ f₂ k ↦ Function.surjInv_eq (hb f₁ f₂).2 k
  have hi : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) φ φ',
      η.conj φ = η.conj φ' → φ = φ' :=
    fun _ _ _ f₁ f₂ φ φ' h ↦ (hb f₁ f₂).1 h
  let D₁ : F₁.DescentData f :=
    { obj := M
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := Function.surjInv (hb f₁ f₂).2 (D₂'.hom q f₁ f₂ hf₁ hf₂)
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        apply hi gf₁ gf₂
        rw [← η.pullHom_conj, hc, hc, D₂'.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := by
        apply hi g g
        rw [hc, conj_id, D₂'.hom_self q g hg]
        rfl
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        apply hi f₁ f₃
        rw [← conj_comp, hc, hc, hc, D₂'.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃] }
  refine ⟨D₁, ⟨DescentData.isoMk e (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ ?_)⟩⟩
  have hk : η.conj (D₁.hom q f₁ f₂ hf₁ hf₂) = D₂'.hom q f₁ f₂ hf₁ hf₂ := hc f₁ f₂ _
  simp only [descentData_obj, descentDataObj_hom, hk, D₂', DescentData.transport_hom,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]

end descentData

/-- **Transfer of effective descent.** If the functors `app X` of `η : CompTrans F₁ F₂` are
equivalences, then `F₂` is a stack for every presieve for which `F₁` is. -/
lemma isStackFor_of_isStackFor [∀ X, (η.app X).IsEquivalence] {S : C} {R : Presieve S}
    (h : F₁.IsStackFor R) : F₂.IsStackFor R := by
  rw [isStackFor_iff] at h ⊢
  exact η.isEquivalence_toDescentData _

end CompTrans

end CategoryTheory.Pseudofunctor
