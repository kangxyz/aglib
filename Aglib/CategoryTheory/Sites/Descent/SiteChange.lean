/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Aglib.CategoryTheory.Sites.Descent.Transfer

/-!
# Descent data along the image of a family under a functor

Let `G : C ⥤ D` and `F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat`. The restriction `F.restrictAlong G` of `F`
along `G` is the composite pseudofunctor `G.op.toPseudofunctor.comp F` on `LocallyDiscrete Cᵒᵖ`;
its `mapComp'` and Mathlib's `pullHom` are those of `F` at the images under `G`
(`restrictAlong_mapComp'_hom_app`, `restrictAlong_pullHom`).

For a family `f i : X i ⟶ S` in `C` with chosen pullbacks `sq`, `sq₃` that `G` maps to pullbacks
(`ChosenPullback.map`, `ChosenPullback₃.map`), descent data for `F.restrictAlong G` relative to
`f` in the sense of Mathlib's `DescentData'` are the same as descent data for `F` relative to
the image family `G.map (f i)` with the image chosen pullbacks
(`restrictDescentData'Equivalence`: the objects and descent morphisms are unchanged, the unit and
cocycle conditions are transported through `restrictAlong_pullHom`). Consequently, if
`(F.restrictAlong G).toDescentData f` is an equivalence, so is
`F.toDescentData (fun i ↦ G.map (f i))`
(`isEquivalence_toDescentData_of_restrictAlong`), and `F` is a stack for the presieve generated
by the image family (`isStackFor_ofArrows_map_of_restrictAlong`).

Everything is stated for arbitrary categories, functors and morphisms; the consumer instantiates it
once (for `G = Spec : CommRingCatᵒᵖ ⥤ Scheme`).
-/

@[expose] public section

noncomputable section

universe t v' v u' u v₁ u₁

namespace CategoryTheory

open Opposite Bicategory Limits Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (G : C ⥤ D)

namespace Limits.ChosenPullback

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} (sq : ChosenPullback f₁ f₂)

/-- The image of a chosen pullback under a functor that maps it to a pullback square. It is
reducible so that its projections are seen as `G.map` of the original ones. -/
abbrev map (hG : IsPullback (G.map sq.p₁) (G.map sq.p₂) (G.map f₁) (G.map f₂)) :
    ChosenPullback (G.map f₁) (G.map f₂) where
  pullback := G.obj sq.pullback
  p₁ := G.map sq.p₁
  p₂ := G.map sq.p₂
  condition := hG.w
  isLimit := hG.isLimit
  p := G.map sq.p
  hp₁ := by rw [← G.map_comp, sq.hp₁]

end Limits.ChosenPullback

namespace Limits.ChosenPullback₃

variable {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  {sq₁₂ : ChosenPullback f₁ f₂} {sq₂₃ : ChosenPullback f₂ f₃} {sq₁₃ : ChosenPullback f₁ f₃}
  (sq₃ : ChosenPullback₃ sq₁₂ sq₂₃ sq₁₃)

/-- The image of a chosen threefold pullback under a functor that maps the four pullback squares
involved to pullback squares. -/
abbrev map (h₁₂ : IsPullback (G.map sq₁₂.p₁) (G.map sq₁₂.p₂) (G.map f₁) (G.map f₂))
    (h₂₃ : IsPullback (G.map sq₂₃.p₁) (G.map sq₂₃.p₂) (G.map f₂) (G.map f₃))
    (h₁₃ : IsPullback (G.map sq₁₃.p₁) (G.map sq₁₃.p₂) (G.map f₁) (G.map f₃))
    (h₃ : IsPullback (G.map sq₃.chosenPullback.p₁) (G.map sq₃.chosenPullback.p₂)
      (G.map sq₁₂.p₂) (G.map sq₂₃.p₁)) :
    ChosenPullback₃ (sq₁₂.map G h₁₂) (sq₂₃.map G h₂₃) (sq₁₃.map G h₁₃) where
  chosenPullback := sq₃.chosenPullback.map G h₃
  p := G.map sq₃.p
  p₁ := G.map sq₃.p₁
  p₃ := G.map sq₃.p₃
  l :=
    { f := G.map sq₃.l.f
      f_p₁ := by
        change G.map sq₃.l.f ≫ G.map sq₁₃.p₁ = G.map sq₃.p₁
        rw [← G.map_comp, sq₃.l.f_p₁]
      f_p₂ := by
        change G.map sq₃.l.f ≫ G.map sq₁₃.p₂ = G.map sq₃.p₃
        rw [← G.map_comp, sq₃.l.f_p₂]
      f_p := by
        change G.map sq₃.l.f ≫ G.map sq₁₃.p = G.map sq₃.p
        rw [← G.map_comp, sq₃.l.f_p] }
  hp₁ := by
    change G.map sq₃.chosenPullback.p₁ ≫ G.map sq₁₂.p₁ = G.map sq₃.p₁
    rw [← G.map_comp, sq₃.hp₁]
  hp₃ := by
    change G.map sq₃.chosenPullback.p₂ ≫ G.map sq₂₃.p₂ = G.map sq₃.p₃
    rw [← G.map_comp, sq₃.hp₃]

end Limits.ChosenPullback₃

namespace Pseudofunctor

variable (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The restriction of `F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat` along `G : C ⥤ D`: the composite
pseudofunctor `X ↦ F.obj ⟨op (G.obj X)⟩`. -/
def restrictAlong : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'} :=
  G.op.toPseudofunctor.comp F

@[simp]
lemma restrictAlong_obj (X : C) :
    (F.restrictAlong G).obj (.mk (op X)) = F.obj (.mk (op (G.obj X))) :=
  rfl

@[simp]
lemma restrictAlong_map_toFunctor {X Y : C} (p : Y ⟶ X) :
    ((F.restrictAlong G).map p.op.toLoc).toFunctor = (F.map (G.map p).op.toLoc).toFunctor :=
  rfl

variable {G F}

/-- The composition isomorphisms of the restricted pseudofunctor are those of `F` at the images
under `G`, as 2-morphisms of `Cat`. -/
lemma restrictAlong_mapComp'_hom {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) :
    ((F.restrictAlong G).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl)).hom =
      (F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (by rw [← h, G.map_comp]; rfl)).hom := by
  subst h
  have e₁ : G.op.toPseudofunctor.map (g ≫ f).op.toLoc =
      G.op.toPseudofunctor.map (f.op.toLoc ≫ g.op.toLoc) := rfl
  have e₂ : G.op.toPseudofunctor.map (f.op.toLoc ≫ g.op.toLoc) =
      G.op.toPseudofunctor.map f.op.toLoc ≫ G.op.toPseudofunctor.map g.op.toLoc :=
    LocallyDiscrete.eq_of_hom (G.op.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom
  have e₃ : (G.map (g ≫ f)).op.toLoc = (G.map f).op.toLoc ≫ (G.map g).op.toLoc := by
    rw [G.map_comp]; rfl
  change F.map₂ (eqToHom e₁) ≫ F.map₂ (eqToHom e₂) ≫
      (F.mapComp (G.op.toPseudofunctor.map f.op.toLoc) (G.op.toPseudofunctor.map g.op.toLoc)).hom =
    F.map₂ (eqToHom e₃) ≫ (F.mapComp (G.map f).op.toLoc (G.map g).op.toLoc).hom
  rw [← Category.assoc, ← F.map₂_comp, eqToHom_trans]
  rfl

lemma restrictAlong_mapComp'_eq {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) :
    (F.restrictAlong G).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← h]; rfl) =
      F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (by rw [← h, G.map_comp]; rfl) :=
  Iso.ext (restrictAlong_mapComp'_hom f g gf h)

lemma restrictAlong_mapComp'_hom_app {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op (G.obj X)))) :
    ((F.restrictAlong G).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M =
      (F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (by rw [← h, G.map_comp]; rfl)).hom.toNatTrans.app M :=
  congrArg (fun α ↦ α.hom.toNatTrans.app M) (restrictAlong_mapComp'_eq f g gf h)

lemma restrictAlong_mapComp'_inv_app {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op (G.obj X)))) :
    ((F.restrictAlong G).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).inv.toNatTrans.app M =
      (F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (by rw [← h, G.map_comp]; rfl)).inv.toNatTrans.app M :=
  congrArg (fun α ↦ α.inv.toNatTrans.app M) (restrictAlong_mapComp'_eq f g gf h)

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's `pullHom` for the restricted pseudofunctor is `pullHom` for `F` at the images
under `G`. The morphism `φ` is typed for the restricted pseudofunctor. -/
lemma restrictAlong_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : (F.restrictAlong G).obj (.mk (op X₁))⦄
    ⦃M₂ : (F.restrictAlong G).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((F.restrictAlong G).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((F.restrictAlong G).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := F.restrictAlong G) φ g gf₁ gf₂ h₁ h₂ =
      pullHom (F := F) (X₁ := G.obj X₁) (X₂ := G.obj X₂) (M₁ := M₁) (M₂ := M₂) (Y := G.obj Y)
        (f₁ := G.map f₁) (f₂ := G.map f₂) φ (G.map g) (G.map gf₁) (G.map gf₂)
        (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) := by
  unfold pullHom
  rw [restrictAlong_mapComp'_hom_app f₁ g gf₁ h₁ M₁, restrictAlong_mapComp'_inv_app f₂ g gf₂ h₂ M₂]
  rfl

-- As in `restrictAlong_pullHom`: the objects of `F.obj _` (a `Cat.of`) must be seen as objects
-- of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- `restrictAlong_pullHom` with the morphism `φ` typed for `F`. -/
lemma restrictAlong_pullHom' ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op (G.obj X₁)))⦄
    ⦃M₂ : F.obj (.mk (op (G.obj X₂)))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map (G.map f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map f₂).op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := F.restrictAlong G) (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (Y := Y)
        (f₁ := f₁) (f₂ := f₂) φ g gf₁ gf₂ h₁ h₂ =
      pullHom (F := F) φ (G.map g) (G.map gf₁) (G.map gf₂)
        (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) :=
  restrictAlong_pullHom (F := F) (G := G) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ g gf₁ gf₂
    h₁ h₂

section CompTransAlong

variable (F₁ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

variable (G F) in
/-- A transformation from `F₁` to `F` over `G`: the data of a `CompTrans F₁ (F.restrictAlong G)`
stated with `F` and `G.map` directly (`CompTransAlong.toCompTrans`), so that a consumer never
elaborates against the composite pseudofunctor. -/
structure CompTransAlong where
  /-- The functor over `X`. -/
  app (X : C) : F₁.obj (.mk (op X)) ⥤ F.obj (.mk (op (G.obj X)))
  /-- The pseudonaturality isomorphism along `f : Y ⟶ X`. -/
  nat {X Y : C} (f : Y ⟶ X) :
    (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅ app X ⋙ (F.map (G.map f).op.toLoc).toFunctor
  /-- Compatibility with the composition isomorphisms. -/
  nat_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
      (M : F₁.obj (.mk (op X))) :
    (nat gf).hom.app M ≫
        (F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
          (by rw [← h, G.map_comp]; rfl)).hom.toNatTrans.app ((app X).obj M) =
      (app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
        (nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (F.map (G.map g).op.toLoc).toFunctor.map ((nat f).hom.app M)

variable {F₁}

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- The transformation `F₁ ⟶ F.restrictAlong G` given by a transformation over `G`. -/
def CompTransAlong.toCompTrans (η : CompTransAlong G F F₁) : CompTrans F₁ (F.restrictAlong G) where
  app := η.app
  nat := η.nat
  nat_comp f g gf h M := by
    rw [restrictAlong_mapComp'_hom_app f g gf h]
    exact η.nat_comp f g gf h M

lemma CompTransAlong.toCompTrans_app (η : CompTransAlong G F F₁) (X : C) :
    η.toCompTrans.app X = η.app X :=
  rfl

variable (G F F₁) in
/-- The proposition of the field `CompTransAlong.nat_comp` for given `app` and `nat`, as a
definition. In development, stating the field through it is what made the field of the
transformation over `Spec` checkable by the kernel. Working hypothesis (not checked against the
kernel implementation): the kernel first compares the arguments of the two applications of
`NatCompAlong`, and so need not unfold the composites of the field. -/
def NatCompAlong (app : ∀ X : C, F₁.obj (.mk (op X)) ⥤ F.obj (.mk (op (G.obj X))))
    (nat : ∀ {X Y : C} (f : Y ⟶ X),
      (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅ app X ⋙ (F.map (G.map f).op.toLoc).toFunctor)
    {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
    (M : F₁.obj (.mk (op X))) : Prop :=
  (nat gf).hom.app M ≫
      (F.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (by rw [← h, G.map_comp]; rfl)).hom.toNatTrans.app ((app X).obj M) =
    (app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
      (nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
      (F.map (G.map g).op.toLoc).toFunctor.map ((nat f).hom.app M)

variable (G F F₁) in
/-- A transformation over `G` from its functors, its pseudonaturality isomorphisms and the
coherence stated through `NatCompAlong`. -/
def CompTransAlong.mk' (app : ∀ X : C, F₁.obj (.mk (op X)) ⥤ F.obj (.mk (op (G.obj X))))
    (nat : ∀ {X Y : C} (f : Y ⟶ X),
      (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅ app X ⋙ (F.map (G.map f).op.toLoc).toFunctor)
    (nat_comp : ∀ {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
      (M : F₁.obj (.mk (op X))), NatCompAlong G F F₁ app nat f g gf h M) :
    CompTransAlong G F F₁ where
  app := app
  nat := nat
  nat_comp f g gf h M := nat_comp f g gf h M

end CompTransAlong

section DescentData'

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  (hsq : ∀ i j, IsPullback (G.map (sq i j).p₁) (G.map (sq i j).p₂) (G.map (f i)) (G.map (f j)))
  (hsq₃ : ∀ i₁ i₂ i₃, IsPullback (G.map (sq₃ i₁ i₂ i₃).chosenPullback.p₁)
    (G.map (sq₃ i₁ i₂ i₃).chosenPullback.p₂) (G.map (sq i₁ i₂).p₂) (G.map (sq i₂ i₃).p₁))

/-- The image chosen pullbacks. -/
abbrev mapChosenPullback (i j : ι) : ChosenPullback (G.map (f i)) (G.map (f j)) :=
  (sq i j).map G (hsq i j)

/-- The image chosen threefold pullbacks. -/
abbrev mapChosenPullback₃ (i₁ i₂ i₃ : ι) :
    ChosenPullback₃ (mapChosenPullback sq hsq i₁ i₂) (mapChosenPullback sq hsq i₂ i₃)
      (mapChosenPullback sq hsq i₁ i₃) :=
  (sq₃ i₁ i₂ i₃).map G (hsq i₁ i₂) (hsq i₂ i₃) (hsq i₁ i₃) (hsq₃ i₁ i₂ i₃)

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The unit condition of `DescentData'` transfers between the restricted pseudofunctor and `F`. -/
lemma pullHom'_self_restrictAlong_iff {obj : ∀ i, F.obj (.mk (op (G.obj (X i))))}
    (hom : ∀ i j, (F.map (G.map (sq i j).p₁).op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (G.map (sq i j).p₂).op.toLoc).toFunctor.obj (obj j)) (i : ι) :
    DescentData'.pullHom' (F := F.restrictAlong G) (sq := sq) hom (f i) (𝟙 (X i)) (𝟙 (X i))
        (Category.id_comp _) (Category.id_comp _) = 𝟙 _ ↔
      DescentData'.pullHom' (F := F) (sq := mapChosenPullback sq hsq) hom (G.map (f i))
        (𝟙 (G.obj (X i))) (𝟙 (G.obj (X i))) (Category.id_comp _) (Category.id_comp _) = 𝟙 _ := by
  let l : X i ⟶ (sq i i).pullback := (sq i i).isPullback.lift (𝟙 _) (𝟙 _) rfl
  have hl₁ : l ≫ (sq i i).p₁ = 𝟙 _ := (sq i i).isPullback.lift_fst _ _ _
  have hl₂ : l ≫ (sq i i).p₂ = 𝟙 _ := (sq i i).isPullback.lift_snd _ _ _
  have key : ∀ (q : G.obj (X i) ⟶ G.obj (X i)) (hq : G.map (𝟙 (X i)) = q)
      (h₁ : q ≫ G.map (f i) = G.map (f i)),
      (DescentData'.pullHom' (F := F.restrictAlong G) (sq := sq) hom (f i) (𝟙 (X i)) (𝟙 (X i))
          (Category.id_comp _) (Category.id_comp _) = 𝟙 _ ↔
        DescentData'.pullHom' (F := F) (sq := mapChosenPullback sq hsq) hom (G.map (f i)) q q
          h₁ h₁ = 𝟙 _) := by
    rintro q rfl h₁
    rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ l (hp₁ := hl₁) (hp₂ := hl₂),
      DescentData'.pullHom'_eq_pullHom _ _ _ _ (G.map l)
        (hp₁ := by rw [← G.map_comp, hl₁]) (hp₂ := by rw [← G.map_comp, hl₂]),
      restrictAlong_pullHom' (hom i i) l (𝟙 _) (𝟙 _) hl₁ hl₂]
    exact Iff.rfl
  exact key _ (G.map_id _) (Category.id_comp _)

-- As for `pullHom'_self_restrictAlong_iff`.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The cocycle condition of `DescentData'` transfers between the restricted pseudofunctor and
`F`. -/
lemma pullHom'_comp_restrictAlong_iff {obj : ∀ i, F.obj (.mk (op (G.obj (X i))))}
    (hom : ∀ i j, (F.map (G.map (sq i j).p₁).op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (G.map (sq i j).p₂).op.toLoc).toFunctor.obj (obj j)) (i₁ i₂ i₃ : ι) :
    DescentData'.pullHom' (F := F.restrictAlong G) (sq := sq) hom (sq₃ i₁ i₂ i₃).p
          (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).w₁ (sq₃ i₁ i₂ i₃).w₂ ≫
        DescentData'.pullHom' (F := F.restrictAlong G) (sq := sq) hom (sq₃ i₁ i₂ i₃).p
          (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ (sq₃ i₁ i₂ i₃).w₂ (sq₃ i₁ i₂ i₃).w₃ =
      DescentData'.pullHom' (F := F.restrictAlong G) (sq := sq) hom (sq₃ i₁ i₂ i₃).p
          (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ (sq₃ i₁ i₂ i₃).w₁ (sq₃ i₁ i₂ i₃).w₃ ↔
    DescentData'.pullHom' (F := F) (sq := mapChosenPullback sq hsq) hom
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₁
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₂
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₁
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₂ ≫
        DescentData'.pullHom' (F := F) (sq := mapChosenPullback sq hsq) hom
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₂
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₃
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₂
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₃ =
      DescentData'.pullHom' (F := F) (sq := mapChosenPullback sq hsq) hom
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₁
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).p₃
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₁
          (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₃ := by
  rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).w₁
      (sq₃ i₁ i₂ i₃).w₂ (sq₃ i₁ i₂ i₃).p₁₂_p₁ (sq₃ i₁ i₂ i₃).p₁₂_p₂,
    DescentData'.pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).w₂
      (sq₃ i₁ i₂ i₃).w₃ (sq₃ i₁ i₂ i₃).p₂₃_p₂ (sq₃ i₁ i₂ i₃).p₂₃_p₃,
    DescentData'.pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).w₁
      (sq₃ i₁ i₂ i₃).w₃ (sq₃ i₁ i₂ i₃).p₁₃_p₁ (sq₃ i₁ i₂ i₃).p₁₃_p₃,
    DescentData'.pullHom'_eq_pullHom _ _ _ _ (G.map (sq₃ i₁ i₂ i₃).p₁₂)
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₁
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₂
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₂]; rfl),
    DescentData'.pullHom'_eq_pullHom _ _ _ _ (G.map (sq₃ i₁ i₂ i₃).p₂₃)
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₂
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₃
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₂]; rfl)
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₃]),
    DescentData'.pullHom'_eq_pullHom _ _ _ _ (G.map (sq₃ i₁ i₂ i₃).p₁₃)
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₁
      (mapChosenPullback₃ sq sq₃ hsq hsq₃ i₁ i₂ i₃).w₃
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₁])
      (by rw [← G.map_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₃]),
    restrictAlong_pullHom' (hom i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ _ _ (sq₃ i₁ i₂ i₃).p₁₂_p₁
      (sq₃ i₁ i₂ i₃).p₁₂_p₂,
    restrictAlong_pullHom' (hom i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ _ _ (sq₃ i₁ i₂ i₃).p₂₃_p₂
      (sq₃ i₁ i₂ i₃).p₂₃_p₃,
    restrictAlong_pullHom' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ (sq₃ i₁ i₂ i₃).p₁₃_p₁
      (sq₃ i₁ i₂ i₃).p₁₃_p₃]
  exact Iff.rfl

variable (F)

/-- Descent data for the restricted pseudofunctor are descent data for `F` relative to the image
family: the functor. -/
@[simps]
def restrictDescentData'Functor :
    (F.restrictAlong G).DescentData' sq sq₃ ⥤
      F.DescentData' (mapChosenPullback sq hsq) (mapChosenPullback₃ sq sq₃ hsq hsq₃) where
  obj D :=
    { obj := D.obj
      hom := D.hom
      pullHom'_hom_self i :=
        (pullHom'_self_restrictAlong_iff F sq hsq D.hom i).1 (D.pullHom'_hom_self i)
      pullHom'_hom_comp i₁ i₂ i₃ :=
        (pullHom'_comp_restrictAlong_iff F sq sq₃ hsq hsq₃ D.hom i₁ i₂ i₃).1
          (D.pullHom'_hom_comp i₁ i₂ i₃) }
  map φ :=
    { hom := φ.hom
      comm := φ.comm }

/-- Descent data for `F` relative to the image family are descent data for the restricted
pseudofunctor: the inverse functor. -/
@[simps]
def corestrictDescentData'Functor :
    F.DescentData' (mapChosenPullback sq hsq) (mapChosenPullback₃ sq sq₃ hsq hsq₃) ⥤
      (F.restrictAlong G).DescentData' sq sq₃ where
  obj D :=
    { obj := D.obj
      hom := D.hom
      pullHom'_hom_self i :=
        (pullHom'_self_restrictAlong_iff F sq hsq D.hom i).2 (D.pullHom'_hom_self i)
      pullHom'_hom_comp i₁ i₂ i₃ :=
        (pullHom'_comp_restrictAlong_iff F sq sq₃ hsq hsq₃ D.hom i₁ i₂ i₃).2
          (D.pullHom'_hom_comp i₁ i₂ i₃) }
  map φ :=
    { hom := φ.hom
      comm := φ.comm }

-- As in Mathlib's `DescentData'.descentDataEquivalence`: the components are `Iso.refl`, and the
-- objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Descent data for the restricted pseudofunctor are descent data for `F` relative to the image
family. -/
@[simps]
def restrictDescentData'Equivalence :
    (F.restrictAlong G).DescentData' sq sq₃ ≌
      F.DescentData' (mapChosenPullback sq hsq) (mapChosenPullback₃ sq sq₃ hsq hsq₃) where
  functor := restrictDescentData'Functor F sq sq₃ hsq hsq₃
  inverse := corestrictDescentData'Functor F sq sq₃ hsq hsq₃
  unitIso := NatIso.ofComponents (fun D ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _)
    (fun _ _ ↦ by dsimp; simp)) (fun φ ↦ by ext i; dsimp; simp)
  counitIso := NatIso.ofComponents (fun D ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _)
    (fun _ _ ↦ by dsimp; simp)) (fun φ ↦ by ext i; dsimp; simp)
  functor_unitIso_comp D := by ext i; dsimp; simp

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category, and
-- `simp` must use the `simps` lemmas of the descent-data constructions.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `toDescentData` of `F` relative to the image family, through the two
`DescentData'` equivalences, is `toDescentData` of the restricted pseudofunctor. -/
def toDescentDataRestrictAlongIso :
    (F.restrictAlong G).toDescentData f ⋙
        (DescentData'.descentDataEquivalence (F.restrictAlong G) sq sq₃).inverse ⋙
        (restrictDescentData'Equivalence F sq sq₃ hsq hsq₃).functor ⋙
        (DescentData'.descentDataEquivalence F (mapChosenPullback sq hsq)
          (mapChosenPullback₃ sq sq₃ hsq hsq₃)).functor ≅
      F.toDescentData (fun i ↦ G.map (f i)) :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk (fun _ ↦ Iso.refl _) (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      obtain ⟨l, hl₁, hl₂⟩ := (mapChosenPullback sq hsq i₁ i₂).isPullback.exists_lift f₁ f₂
        (by rw [hf₁, hf₂])
      dsimp
      rw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id,
        DescentData'.pullHom'_eq_pullHom _ _ _ _ l (hp₁ := hl₁) (hp₂ := hl₂)]
      dsimp
      rw [restrictAlong_mapComp'_inv_app (f i₁) (sq i₁ i₂).p₁ (sq i₁ i₂).p (sq i₁ i₂).hp₁ M,
        restrictAlong_mapComp'_hom_app (f i₂) (sq i₁ i₂).p₂ (sq i₁ i₂).p (sq i₁ i₂).hp₂ M]
      exact ((DescentData.ofObj (F := F) (f := fun i ↦ G.map (f i)) M).pullHom_hom l
        (G.map (sq i₁ i₂).p) q
        (by rw [← hf₁, ← hl₁, Category.assoc, ← (sq i₁ i₂).hp₁, G.map_comp])
        (G.map (sq i₁ i₂).p₁) (G.map (sq i₁ i₂).p₂) (by rw [← G.map_comp, (sq i₁ i₂).hp₁])
        (by rw [← G.map_comp, (sq i₁ i₂).hp₂]) f₁ f₂ hl₁ hl₂).symm))
    (fun φ ↦ by
      ext i
      dsimp
      simp)

include sq sq₃ hsq hsq₃ in
/-- If `toDescentData` of the restricted pseudofunctor is an equivalence relative to `f`, then
`toDescentData` of `F` is an equivalence relative to the image family. -/
lemma isEquivalence_toDescentData_of_restrictAlong
    [((F.restrictAlong G).toDescentData f).IsEquivalence] :
    (F.toDescentData (fun i ↦ G.map (f i))).IsEquivalence := by
  have h : ((F.restrictAlong G).toDescentData f ⋙
      (DescentData'.descentDataEquivalence (F.restrictAlong G) sq sq₃).inverse ⋙
      (restrictDescentData'Equivalence F sq sq₃ hsq hsq₃).functor ⋙
      (DescentData'.descentDataEquivalence F (mapChosenPullback sq hsq)
        (mapChosenPullback₃ sq sq₃ hsq hsq₃)).functor).IsEquivalence :=
    (((F.restrictAlong G).toDescentData f).asEquivalence.trans
      ((DescentData'.descentDataEquivalence (F.restrictAlong G) sq sq₃).symm.trans
        ((restrictDescentData'Equivalence F sq sq₃ hsq hsq₃).trans
          (DescentData'.descentDataEquivalence F (mapChosenPullback sq hsq)
            (mapChosenPullback₃ sq sq₃ hsq hsq₃))))).isEquivalence_functor
  exact @Functor.isEquivalence_of_iso _ _ _ _ _ _
    (toDescentDataRestrictAlongIso F sq sq₃ hsq hsq₃) h

include sq sq₃ hsq hsq₃ in
/-- **Site change for effective descent.** If the restricted pseudofunctor is a stack for the
presieve generated by `f`, then `F` is a stack for the presieve generated by the image family. -/
lemma isStackFor_ofArrows_map_of_restrictAlong
    (h : (F.restrictAlong G).IsStackFor (Presieve.ofArrows X f)) :
    F.IsStackFor (Presieve.ofArrows (fun i ↦ G.obj (X i)) (fun i ↦ G.map (f i))) := by
  rw [isStackFor_ofArrows_iff] at h ⊢
  exact isEquivalence_toDescentData_of_restrictAlong F sq sq₃ hsq hsq₃

end DescentData'

end Pseudofunctor

end CategoryTheory
