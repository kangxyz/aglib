/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.AffineStack

/-!
# The coherence of the comparison transformation over `Spec`, and affine descent

This file proves the coherence field of the transformation over `Spec` from the module
pseudofunctor to the quasi-coherent pseudofunctor with components `specTransApp` and
pseudonaturality isomorphisms `specTransNat` (`specNatCompAlong`), builds the transformation
(`specCompTransAlong`), and deduces the affine stack theorem
`isStackFor_quasicoherentPseudofunctor_singleton_specMap` from the conditional theorem of
`AffineStack.lean`.

The coherence field `nat_comp` of a `Pseudofunctor.CompTransAlong G Pr.fullsubcategory F₁` is
reduced, generically, to an identity in the ambient pseudofunctor (`NatCompAmbient`,
`natComp_of_natCompAmbient`) and, for `pullbackPseudofunctor`, to an identity written with
Mathlib's `pullbackCongr` and `pullbackComp` (`NatCompPullback`,
`natCompAmbient_of_natCompPullback`); `natCompAlong_of_natCompPullback` composes the two, with the
field stated through the definition `Pseudofunctor.NatCompAlong`.

The content of the coherence is Aglib's `tildePullbackIso_comp_hom_app`. It is transported to the
field by `Pseudofunctor.natCompAlong_of_transport`, a lemma for an arbitrary functor
`G : CommRingCatᵒᵖ ⥤ Scheme` and arbitrary `app`, `nat`: its hypothesis is the identity of
`tildePullbackIso_comp_hom_app` with the schemes, the morphisms `Spec.map _`, the functors
`tilde.functor _` and the isomorphisms `tildePullbackIso _` replaced by variables, and the
identifications of these variables with `G`, `app` and `nat` are equations of schemes and `HEq`s
of morphisms, objects and components. Its proof substitutes the variables and rearranges with
`comp_eq_of_leaves_heq`. At `G = Scheme.Spec` (`specNatCompAlong`) the hypothesis is
`tildePullbackIso_comp_hom_app` itself and every identification is `rfl` or `HEq.rfl`.

Kernel note. In development, kernel comparisons at `Spec` of two composites whose factors or
implicit objects differ in presentation, and of components of `pullbackCongr` or `mapComp'` with
differently presented arguments, timed out or exhausted memory, while comparisons of components
of `tildePullbackIso`, `specTransNat`, and of objects and morphisms of schemes, took seconds. The
proofs here therefore keep every comparison at `Spec` structural or between such components, and
they state the field through the definitions `NatCompAlong` and `NatCompPullback`. All
substitutions of one presentation for another happen in the generic proofs, where the scheme
morphisms are variables. Working hypothesis for these observations (not checked against the
kernel implementation): composites and components are projections, which the kernel unfolds
instead of comparing their arguments, and the reduction of the `Eq.rec` inside `pullbackCongr`
unfolds `Spec.map`; whereas for two applications of a definition such as `NatCompAlong` the
kernel first compares the arguments.
-/

@[expose] public section

noncomputable section

universe u v' v u' u₁ v₁ w

open CategoryTheory Opposite Bicategory Limits CommRingCat

namespace CategoryTheory

/-- The rearrangement in the shape of `nat_comp`, with every leaf of the target identity and of
the input identity `w` given separately and related by equations: from
`w : c₁' ≫ c₂' ≫ φh ≫ βh = γh ≫ ε`, the inverse relations `hγ`, `hφ`, `hβ` and the leaf equations,
`n₃ ≫ c₁ ≫ c₂ = m ≫ n₂ ≫ n₁`. -/
theorem comp_eq_of_leaves {D : Type w} [Category.{v} D] {W U₀ U V Y Z : D}
    {c₁' : W ⟶ U₀} {c₂' : U₀ ⟶ U} {φh : U ⟶ V} {βh : V ⟶ Z} {γh : W ⟶ Y} {ε : Y ⟶ Z}
    (w : c₁' ≫ c₂' ≫ φh ≫ βh = γh ≫ ε)
    {n₃ : Y ⟶ W} (γi : Y ⟶ W) (hn₃ : n₃ = γi) (hγ : γi ≫ γh = 𝟙 Y)
    {c₁ : W ⟶ U₀} (hc₁ : c₁ = c₁') {c₂ : U₀ ⟶ U} (hc₂ : c₂ = c₂')
    {n₁ : V ⟶ U} (φi : V ⟶ U) (hn₁ : n₁ = φi) (hφ : φh ≫ φi = 𝟙 U)
    {n₂ : Z ⟶ V} (βi : Z ⟶ V) (hn₂ : n₂ = βi) (hβ : βh ≫ βi = 𝟙 V)
    {m : Y ⟶ Z} (hm : m = ε) :
    n₃ ≫ c₁ ≫ c₂ = m ≫ n₂ ≫ n₁ := by
  rw [hn₃, hc₁, hc₂, hn₁, hn₂, hm]
  have e₁ : c₁' ≫ c₂' = c₁' ≫ c₂' ≫ φh ≫ βh ≫ βi ≫ φi := by
    rw [reassoc_of% hβ, hφ, Category.comp_id]
  rw [e₁, reassoc_of% w, reassoc_of% hγ]

/-- `comp_eq_of_leaves` with the objects and leaves of the target identity related to those of
the input identity `w` by equations of objects and `HEq`s of morphisms. -/
theorem comp_eq_of_leaves_heq {D : Type w} [Category.{v} D] {W' U₀' U' V' Y' Z' : D}
    {c₁' : W' ⟶ U₀'} {c₂' : U₀' ⟶ U'} {φh : U' ⟶ V'} {βh : V' ⟶ Z'} {γh : W' ⟶ Y'}
    {ε : Y' ⟶ Z'} (w : c₁' ≫ c₂' ≫ φh ≫ βh = γh ≫ ε)
    {W U₀ U V Y Z : D} (hW : W = W') (hU₀ : U₀ = U₀') (hU : U = U') (hV : V = V')
    (hY : Y = Y') (hZ : Z = Z')
    {n₃ : Y ⟶ W} {γi : Y' ⟶ W'} (hn₃ : HEq n₃ γi) (hγ : γi ≫ γh = 𝟙 Y')
    {c₁ : W ⟶ U₀} (hc₁ : HEq c₁ c₁') {c₂ : U₀ ⟶ U} (hc₂ : HEq c₂ c₂')
    {n₁ : V ⟶ U} {φi : V' ⟶ U'} (hn₁ : HEq n₁ φi) (hφ : φh ≫ φi = 𝟙 U')
    {n₂ : Z ⟶ V} {βi : Z' ⟶ V'} (hn₂ : HEq n₂ βi) (hβ : βh ≫ βi = 𝟙 V')
    {m : Y ⟶ Z} (hm : HEq m ε) :
    n₃ ≫ c₁ ≫ c₂ = m ≫ n₂ ≫ n₁ := by
  subst hW hU₀ hU hV hY hZ
  obtain rfl := eq_of_heq hn₃
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₂
  obtain rfl := eq_of_heq hn₁
  obtain rfl := eq_of_heq hn₂
  obtain rfl := eq_of_heq hm
  exact comp_eq_of_leaves w _ rfl hγ rfl rfl _ rfl hφ _ rfl hβ rfl

/-- The images under a functor of two morphisms with equal sources, equal targets and `HEq`. -/
theorem Functor.map_heq_of_heq {C : Type u₁} [Category.{v₁} C] {D : Type u} [Category.{v} D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B') {a : A ⟶ B} {a' : A' ⟶ B'}
    (ha : HEq a a') : HEq (F.map a) (F.map a') := by
  subst hA hB
  obtain rfl := eq_of_heq ha
  rfl

namespace Pseudofunctor

section Generic

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (G : C ⥤ D)
  {P : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u'}} (Pr : P.ObjectProperty) [Pr.IsClosedUnderMapObj]
  (F₁ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  (app : ∀ X : C, F₁.obj (.mk (op X)) ⥤ Pr.fullsubcategory.obj (.mk (op (G.obj X))))
  (nat : ∀ {X Y : C} (f : Y ⟶ X),
    (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅
      app X ⋙ (Pr.fullsubcategory.map (G.map f).op.toLoc).toFunctor)

/-- The coherence `CompTransAlong.nat_comp` for `F := Pr.fullsubcategory`, stated in the ambient
pseudofunctor `P` (the `.hom` components), for given proofs `p`, `q` of the composite equations. -/
def NatCompAmbient {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (p : (G.map f).op.toLoc ≫ (G.map g).op.toLoc = (G.map gf).op.toLoc)
    (q : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc) (M : F₁.obj (.mk (op X))) : Prop :=
  ((nat gf).hom.app M).hom ≫
      (P.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        p).hom.toNatTrans.app ((app X).obj M).obj =
    ((app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        q).hom.toNatTrans.app M)).hom ≫
      ((nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M)).hom ≫
      (P.map (G.map g).op.toLoc).toFunctor.map ((nat f).hom.app M).hom

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- The coherence field of a `CompTransAlong G Pr.fullsubcategory F₁` follows from its ambient
form. The conclusion is the text of `CompTransAlong.nat_comp`, with the proofs `p`, `q` implicit,
so that an application against the field unifies them with the field's own proofs. -/
theorem natComp_of_natCompAmbient {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    {p : (G.map f).op.toLoc ≫ (G.map g).op.toLoc = (G.map gf).op.toLoc}
    {q : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc} (M : F₁.obj (.mk (op X)))
    (w : NatCompAmbient G Pr F₁ app nat f g gf p q M) :
    (nat gf).hom.app M ≫
        (Pr.fullsubcategory.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
          p).hom.toNatTrans.app ((app X).obj M) =
      (app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          q).hom.toNatTrans.app M) ≫
        (nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M) ≫
        (Pr.fullsubcategory.map (G.map g).op.toLoc).toFunctor.map ((nat f).hom.app M) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.fullsubcategory_mapComp'_hom_app_hom,
    ObjectProperty.fullsubcategory_map_map_hom]
  exact w

end Generic

section Schemes

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {C : Type u₁} [Category.{v₁} C] (G : C ⥤ Scheme.{u})
  (Pr : pullbackPseudofunctor.{u}.ObjectProperty) [Pr.IsClosedUnderMapObj]
  (F₁ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1})
  (app : ∀ X : C, F₁.obj (.mk (op X)) ⥤ Pr.fullsubcategory.obj (.mk (op (G.obj X))))
  (nat : ∀ {X Y : C} (f : Y ⟶ X),
    (F₁.map f.op.toLoc).toFunctor ⋙ app Y ≅
      app X ⋙ (Pr.fullsubcategory.map (G.map f).op.toLoc).toFunctor)

/-- The ambient coherence for `pullbackPseudofunctor`, with Mathlib's `pullbackCongr` and
`pullbackComp` in place of `mapComp'`, for a given proof `hc` of the composite equation. -/
def NatCompPullback {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (hc : G.map g ≫ G.map f = G.map gf) (q : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc)
    (M : F₁.obj (.mk (op X))) : Prop :=
  ((nat gf).hom.app M).hom ≫
      (pullbackCongr hc.symm).hom.app ((app X).obj M).obj ≫
      (pullbackComp (G.map g) (G.map f)).inv.app ((app X).obj M).obj =
    ((app Z).map ((F₁.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        q).hom.toNatTrans.app M)).hom ≫
      ((nat g).hom.app ((F₁.map f.op.toLoc).toFunctor.obj M)).hom ≫
      (Scheme.Modules.pullback (G.map g)).map ((nat f).hom.app M).hom

-- The objects of `F.obj _` (a `Cat.of`) must be seen as objects of the underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- The ambient coherence in `mapComp'` form from the `pullbackCongr`/`pullbackComp` form. -/
theorem natCompAmbient_of_natCompPullback {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (hc : G.map g ≫ G.map f = G.map gf)
    {p : (G.map f).op.toLoc ≫ (G.map g).op.toLoc = (G.map gf).op.toLoc}
    {q : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc} (M : F₁.obj (.mk (op X)))
    (w : NatCompPullback G Pr F₁ app nat f g gf hc q M) :
    NatCompAmbient G Pr F₁ app nat f g gf p q M := by
  unfold NatCompPullback at w
  unfold NatCompAmbient
  rw [pullbackPseudofunctor_mapComp'_hom_app (G.map f) (G.map g) (G.map gf) hc]
  exact w

/-- The coherence of a `CompTransAlong G Pr.fullsubcategory F₁`, stated through `NatCompAlong`,
from the `pullbackCongr`/`pullbackComp` form, for any proofs `hc`, `q` of the composite
equations. -/
theorem natCompAlong_of_natCompPullback {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F₁.obj (.mk (op X))) (hc : G.map g ≫ G.map f = G.map gf)
    (q : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc)
    (w : NatCompPullback G Pr F₁ app nat f g gf hc q M) :
    NatCompAlong G Pr.fullsubcategory F₁ app nat f g gf h M :=
  natComp_of_natCompAmbient G Pr F₁ app nat f g gf M
    (natCompAmbient_of_natCompPullback G Pr F₁ app nat f g gf hc M w)

end Schemes

end Pseudofunctor

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The ring-level bridge for morphisms of `CommRingCatᵒᵖ` and a given proof `q`: the composition
isomorphism of the module pseudofunctor is `extendScalarsComp`. -/
lemma moduleCat_mapComp'_hom_app_op' {X Y Z : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : f.op.toLoc ≫ g.op.toLoc = (g ≫ f).op.toLoc)
    (M : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X))) :
    (moduleCatExtendScalarsPseudofunctorOpOp.{u}.mapComp' f.op.toLoc g.op.toLoc
        (g ≫ f).op.toLoc q).hom.toNatTrans.app M =
      (ModuleCat.extendScalarsComp f.unop.hom g.unop.hom).hom.app M :=
  (moduleCatExtendScalarsPseudofunctorOpOp_mapComp'_hom_app' f.unop g.unop
      (f.unop ≫ g.unop) rfl q M).trans
    (by simp only [ModuleCat.extendScalarsComp', eqToIso_refl, Iso.refl_trans]; rfl)

/-- The components of `pullbackCongr` at equal objects, for any two proofs. -/
lemma pullbackCongr_hom_app_heq {X Y : Scheme.{u}} {x y : X ⟶ Y} (p p' : x = y)
    {A A' : Y.Modules} (hA : A = A') :
    HEq ((pullbackCongr p).hom.app A) ((pullbackCongr p').hom.app A') := by
  subst hA
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Pseudofunctor

section Transport

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable (G : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u})
  (Pr : pullbackPseudofunctor.{u}.ObjectProperty) [Pr.IsClosedUnderMapObj]
  (app : ∀ X : CommRingCat.{u}ᵒᵖ, moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X)) ⥤
    Pr.fullsubcategory.obj (.mk (op (G.obj X))))
  (nat : ∀ {X Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X),
    (moduleCatExtendScalarsPseudofunctorOpOp.{u}.map f.op.toLoc).toFunctor ⋙ app Y ≅
      app X ⋙ (Pr.fullsubcategory.map (G.map f).op.toLoc).toFunctor)

/-- **Transport of the composition identity of `tildePullbackIso` to the coherence field.** Let
`G : CommRingCatᵒᵖ ⥤ Scheme` and `app`, `nat` be the data of a transformation over `G` from the
module pseudofunctor to a full subcategory of `pullbackPseudofunctor`. Let schemes `X₀ Y₀ Z₀`,
morphisms `x = y₁ ≫ y₂`, functors `tR tS tT` from the module categories and isomorphisms
`τa τb τab` (in the roles of `Spec _`, `Spec.map _`, `tilde.functor _` and `tildePullbackIso _`)
satisfy the identity `w` of `tildePullbackIso_comp_hom_app`, and be identified with `G`, `app` and
`nat`: the schemes by equations, the morphisms of schemes, the objects and morphisms in the image
of `app` and the components of `nat` by `HEq`s. Then the coherence `NatCompAlong` holds. -/
theorem natCompAlong_of_transport {X Y Z : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) (g : Z ⟶ Y)
    (gf : Z ⟶ X) (h : g ≫ f = gf) (M : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X)))
    {X₀ Y₀ Z₀ : Scheme.{u}} {x : Z₀ ⟶ X₀} {y₁ : Z₀ ⟶ Y₀} {y₂ : Y₀ ⟶ X₀} {e : x = y₁ ≫ y₂}
    {tR : ModuleCat.{u} X.unop ⥤ X₀.Modules} {tS : ModuleCat.{u} Y.unop ⥤ Y₀.Modules}
    {tT : ModuleCat.{u} Z.unop ⥤ Z₀.Modules}
    {τa : tR ⋙ Scheme.Modules.pullback y₂ ≅ ModuleCat.extendScalars f.unop.hom ⋙ tS}
    {τb : tS ⋙ Scheme.Modules.pullback y₁ ≅ ModuleCat.extendScalars g.unop.hom ⋙ tT}
    {τab : tR ⋙ Scheme.Modules.pullback x ≅ ModuleCat.extendScalars (f.unop ≫ g.unop).hom ⋙ tT}
    (w : (pullbackCongr e).hom.app (tR.obj M) ≫ (pullbackComp y₁ y₂).inv.app (tR.obj M) ≫
        (Scheme.Modules.pullback y₁).map (τa.hom.app M) ≫
          τb.hom.app ((ModuleCat.extendScalars f.unop.hom).obj M) =
      τab.hom.app M ≫ tT.map ((ModuleCat.extendScalarsComp f.unop.hom g.unop.hom).hom.app M))
    (hX : G.obj X = X₀) (hY : G.obj Y = Y₀) (hZ : G.obj Z = Z₀)
    (hx : HEq (G.map (g ≫ f)) x) (hy₁ : HEq (G.map g) y₁) (hy₂ : HEq (G.map f) y₂)
    (hoX : ∀ N : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X)),
      HEq ((app X).obj N).obj (tR.obj N))
    (hoY : ∀ N : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op Y)),
      HEq ((app Y).obj N).obj (tS.obj N))
    (hoZ : ∀ N : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op Z)),
      HEq ((app Z).obj N).obj (tT.obj N))
    (hmZ : ∀ {N₁ N₂ : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op Z))}
      (φ : N₁ ⟶ N₂), HEq ((app Z).map φ).hom (tT.map φ))
    (hn₁ : HEq ((nat f).hom.app M).hom (τa.inv.app M))
    (hn₂ : HEq ((nat g).hom.app
        ((moduleCatExtendScalarsPseudofunctorOpOp.{u}.map f.op.toLoc).toFunctor.obj M)).hom
      (τb.inv.app ((ModuleCat.extendScalars f.unop.hom).obj M)))
    (hn₃ : HEq ((nat (g ≫ f)).hom.app M).hom (τab.inv.app M)) :
    NatCompAlong G Pr.fullsubcategory moduleCatExtendScalarsPseudofunctorOpOp.{u} app nat
      f g gf h M := by
  subst h hX hY hZ
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy₁
  obtain rfl := eq_of_heq hy₂
  refine natCompAlong_of_natCompPullback G Pr _ app nat f g (g ≫ f) rfl M e.symm rfl ?_
  unfold NatCompPullback
  refine comp_eq_of_leaves_heq w ?_ ?_ ?_ ?_ ?_ ?_ hn₃ (Iso.inv_hom_id_app _ _)
    (pullbackCongr_hom_app_heq _ _ (eq_of_heq (hoX M)))
    (congr_arg_heq (fun A ↦ (pullbackComp (G.map g) (G.map f)).inv.app A) (eq_of_heq (hoX M)))
    (Functor.map_heq_of_heq _ (eq_of_heq (hoY _))
      (congrArg (Scheme.Modules.pullback (G.map f)).obj (eq_of_heq (hoX M))) hn₁)
    ((Scheme.Modules.pullback (G.map g)).mapIso (τa.app M)).hom_inv_id
    hn₂ (Iso.hom_inv_id_app _ _)
    ((hmZ _).trans (heq_of_eq (congrArg tT.map (moduleCat_mapComp'_hom_app_op' f g rfl M))))
  · exact congrArg (Scheme.Modules.pullback (G.map (g ≫ f))).obj (eq_of_heq (hoX M))
  · exact congrArg (Scheme.Modules.pullback (G.map g ≫ G.map f)).obj (eq_of_heq (hoX M))
  · exact congrArg (Scheme.Modules.pullback (G.map f) ⋙ Scheme.Modules.pullback (G.map g)).obj
      (eq_of_heq (hoX M))
  · exact congrArg (Scheme.Modules.pullback (G.map g)).obj (eq_of_heq (hoY _))
  · exact eq_of_heq (hoZ _)
  · exact eq_of_heq (hoZ _)

end Transport

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Pseudofunctor

/-- **The coherence of `specTransNat` with the composition isomorphisms**: the field `nat_comp`
of the transformation over `Spec` with components `specTransApp` and pseudonaturality
isomorphisms `specTransNat`. It is `tildePullbackIso_comp_hom_app` transported by
`natCompAlong_of_transport`, all of whose identifications hold by `rfl`. -/
theorem specNatCompAlong {X Y Z : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : moduleCatExtendScalarsPseudofunctorOpOp.{u}.obj (.mk (op X))) :
    NatCompAlong Scheme.Spec quasicoherentPseudofunctor.{u}
      moduleCatExtendScalarsPseudofunctorOpOp.{u} specTransApp specTransNat f g gf h M :=
  natCompAlong_of_transport Scheme.Spec pullbackPseudofunctor.isQuasicoherent.{u} specTransApp
    specTransNat f g gf h M
    (tildePullbackIso_comp_hom_app f.unop g.unop (Spec.map_comp _ _) M)
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl)
    (fun _ ↦ HEq.rfl) HEq.rfl HEq.rfl HEq.rfl

/-- The comparison transformation over `Spec : CommRingCatᵒᵖ ⥤ Scheme` from the module
pseudofunctor to the quasi-coherent pseudofunctor: components `specTransApp` (Mathlib's
`tildeEquiv.functor`), pseudonaturality isomorphisms `specTransNat` (Aglib's `tildePullbackIso`)
and coherence `specNatCompAlong`. -/
def specCompTransAlong : Pseudofunctor.CompTransAlong Scheme.Spec quasicoherentPseudofunctor.{u}
    moduleCatExtendScalarsPseudofunctorOpOp.{u} :=
  CompTransAlong.mk' Scheme.Spec quasicoherentPseudofunctor.{u}
    moduleCatExtendScalarsPseudofunctorOpOp.{u} specTransApp specTransNat specNatCompAlong

instance (X : CommRingCat.{u}ᵒᵖ) : (specCompTransAlong.{u}.toCompTrans.app X).IsEquivalence :=
  inferInstanceAs (specTransApp.{u} X).IsEquivalence

/-- **Faithfully flat descent of quasi-coherent sheaves on affine schemes.** For a faithfully flat
ring map `f : A ⟶ B`, the pseudofunctor of quasi-coherent sheaves is a stack for the singleton
presieve of `Spec.map f : Spec B ⟶ Spec A`: the conditional theorem
`isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong` at
`specCompTransAlong`. -/
theorem isStackFor_quasicoherentPseudofunctor_singleton_specMap {A B : CommRingCat.{u}}
    (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    quasicoherentPseudofunctor.{u}.IsStackFor (Presieve.singleton (Spec.map f)) :=
  isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong specCompTransAlong.{u}
    f hf

end AlgebraicGeometry.Scheme.Modules
