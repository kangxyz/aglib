/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Full subpseudofunctors cut out by local properties

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and let `P : F.ObjectProperty` be closed under the
functors `F.map` and under isomorphisms. Descent data for `P.fullsubcategory` relative to a
family `f i : X i ⟶ S` are descent data for `F` whose objects satisfy `P`
(`ObjectProperty.descentDataForget`, fully faithful).

If `F.toDescentData f` is an equivalence and `P` is local along `f` (an object whose pullbacks
along all `f i` satisfy `P` satisfies `P`), then `P.fullsubcategory.toDescentData f` is an
equivalence (`ObjectProperty.isEquivalence_toDescentData_fullsubcategory`); full faithfulness
transfers without locality (`ObjectProperty.isPrestack_fullsubcategory`). Consequently, if
`F` is a stack for a Grothendieck topology `J` and `P` is local for the covering sieves of
`J`, then `P.fullsubcategory` is a stack for `J` (`ObjectProperty.isStack_fullsubcategory`).

**Nested substacks.** Let `P ≤ Q` be object properties of `F`, closed under the functors `F.map`.
`isStack_fullsubcategory` needs the ambient `F` to be a stack; the following variants only need
the ambient stack `Q.fullsubcategory`:

* `ObjectProperty.descentDataLift`: a descent datum for `F` whose objects satisfy `Q` is a descent
  datum for `Q.fullsubcategory` (with the same objects and morphisms);
* `ObjectProperty.isEquivalence_toDescentData_fullsubcategory_of_le`: if
  `Q.fullsubcategory.toDescentData f` is an equivalence and `P` is closed under isomorphisms and
  local along `f` for objects satisfying `Q`, then `P.fullsubcategory.toDescentData f` is an
  equivalence;
* `ObjectProperty.isStack_fullsubcategory_of_le`: the same for all covering sieves of a topology
  `J`. Consumer: line bundles inside quasi-coherent sheaves
  (`Descent/Modules/Fppf/LineBundleStack.lean`).

This is the statement recorded as a TODO in Mathlib's
`Mathlib/CategoryTheory/Bicategory/Functor/Cat/ObjectProperty.lean` (module docstring, "TODO");
locality is passed as an explicit hypothesis rather than a new typeclass. It is the formal step
used in the proof of Stacks Project (revision a04446e5), Tag 023E, where effectivity for
quasi-coherent sheaves follows from
gluing of sheaves "and the fact that being quasi-coherent is a local property".
-/

@[expose] public section

universe t v' v u' u w₁ v₁ u₁

namespace CategoryTheory.Pseudofunctor.ObjectProperty

open Opposite Bicategory LocallyDiscreteOpToCat

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {G : Pseudofunctor B Cat.{v', u'}}
  (Q : G.ObjectProperty) [Q.IsClosedUnderMapObj]

@[simp]
lemma fullsubcategory_mapComp'_hom_app_hom {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (M : Q.Obj X) :
    ((Q.fullsubcategory.mapComp' f g fg h).hom.toNatTrans.app M).hom =
      (G.mapComp' f g fg h).hom.toNatTrans.app M.obj := by
  subst h
  simp only [mapComp'_eq_mapComp]
  rfl

@[simp]
lemma fullsubcategory_mapComp'_inv_app_hom {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (M : Q.Obj X) :
    ((Q.fullsubcategory.mapComp' f g fg h).inv.toNatTrans.app M).hom =
      (G.mapComp' f g fg h).inv.toNatTrans.app M.obj := by
  subst h
  simp only [mapComp'_eq_mapComp]
  rfl

@[simp]
lemma fullsubcategory_map_map_hom {X Y : B} (f : X ⟶ Y) {M N : Q.Obj X} (φ : M ⟶ N) :
    ((Q.fullsubcategory.map f).toFunctor.map φ).hom = (G.map f).toFunctor.map φ.hom :=
  rfl

end

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (P : F.ObjectProperty) [P.IsClosedUnderMapObj]

lemma fullsubcategory_pullHom_hom ⦃X₁ X₂ : C⦄ ⦃M₁ : P.Obj (.mk (op X₁))⦄
    ⦃M₂ : P.Obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (P.fullsubcategory.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (P.fullsubcategory.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom (F := P.fullsubcategory) φ g gf₁ gf₂ hgf₁ hgf₂).hom =
      pullHom (F := F) φ.hom g gf₁ gf₂ hgf₁ hgf₂ := by
  subst hgf₁ hgf₂
  rfl

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Descent data for the full subpseudofunctor `P.fullsubcategory` are descent data for `F`. -/
def descentDataForget : P.fullsubcategory.DescentData f ⥤ F.DescentData f where
  obj D :=
    { obj i := (D.obj i).obj
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).hom
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
        (fullsubcategory_pullHom_hom P _ g gf₁ gf₂ hgf₁ hgf₂).symm.trans
          (congrArg InducedCategory.Hom.hom
            (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂))
      hom_self Y q i g hg := by
        rw [D.hom_self q g hg]
        rfl
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        rw [← D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]
        rfl }
  map {D₁ D₂} φ :=
    { hom i := (φ.hom i).hom
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm q f₁ f₂ hf₁ hf₂
        exact congrArg InducedCategory.Hom.hom this }

/-- The forgetful functor on descent data is fully faithful. -/
def fullyFaithfulDescentDataForget : (descentDataForget P f).FullyFaithful where
  preimage {D₁ D₂} ψ :=
    { hom i := ObjectProperty.homMk (ψ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := InducedCategory.hom_ext (ψ.comm q f₁ f₂ hf₁ hf₂) }

instance : (descentDataForget P f).Full := (fullyFaithfulDescentDataForget P f).full

instance : (descentDataForget P f).Faithful := (fullyFaithfulDescentDataForget P f).faithful

-- The components are `Iso.refl`: the objects of `P.fullsubcategory.obj _` (a `Cat.of`) must be
-- seen as objects of `P.Obj _`, which needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the property after `toDescentData` is `toDescentData` after forgetting. -/
def toDescentDataCompDescentDataForgetIso :
    P.fullsubcategory.toDescentData f ⋙ descentDataForget P f ≅
      (P.prop (.mk (op S))).ι ⋙ F.toDescentData f :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by
    intro M N φ
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- If `F.toDescentData f` is fully faithful, so is `P.fullsubcategory.toDescentData f`. -/
def fullyFaithfulToDescentDataFullsubcategory (h : (F.toDescentData f).FullyFaithful) :
    (P.fullsubcategory.toDescentData f).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := descentDataForget P f)
    (((P.prop (.mk (op S))).fullyFaithfulι.comp h).ofIso
      (toDescentDataCompDescentDataForgetIso P f).symm)

/-- A full subpseudofunctor of a prestack is a prestack. -/
theorem isPrestack_fullsubcategory {J : GrothendieckTopology C} [F.IsPrestack J] :
    P.fullsubcategory.IsPrestack J :=
  IsPrestack.of_isPrestackFor fun _ R hR ↦
    ⟨⟨fullyFaithfulToDescentDataFullsubcategory P _ (F.isPrestackFor' R hR).fullyFaithful⟩⟩

variable {f} in
/-- If `F.toDescentData f` is an equivalence and `P` is closed under isomorphisms and local
along `f`, then `P.fullsubcategory.toDescentData f` is an equivalence. -/
lemma isEquivalence_toDescentData_fullsubcategory [P.IsClosedUnderIsomorphisms]
    [(F.toDescentData f).IsEquivalence]
    (hP : ∀ M : F.obj (.mk (op S)),
      (∀ i, P.prop _ ((F.map (f i).op.toLoc).toFunctor.obj M)) → P.prop _ M) :
    (P.fullsubcategory.toDescentData f).IsEquivalence := by
  let e := toDescentDataCompDescentDataForgetIso P f
  have hff : (P.fullsubcategory.toDescentData f ⋙ descentDataForget P f).FullyFaithful :=
    (((P.prop (.mk (op S))).fullyFaithfulι.comp
      (Functor.FullyFaithful.ofFullyFaithful (F.toDescentData f)))).ofIso e.symm
  have hff' := Functor.FullyFaithful.ofCompFaithful hff
  have := hff'.full
  have := hff'.faithful
  have : (P.fullsubcategory.toDescentData f).EssSurj := ⟨fun D ↦ by
    let D₀ := (descentDataForget P f).obj D
    let M := (F.toDescentData f).objPreimage D₀
    let α : (F.toDescentData f).obj M ≅ D₀ := (F.toDescentData f).objObjPreimageIso D₀
    have hM : P.prop _ M := hP M (fun i ↦
      (P.prop _).prop_of_iso
        { hom := α.inv.hom i
          inv := α.hom.hom i
          hom_inv_id := congrArg (fun φ ↦ DescentData.Hom.hom φ i) α.inv_hom_id
          inv_hom_id := congrArg (fun φ ↦ DescentData.Hom.hom φ i) α.hom_inv_id }
        (by exact (D.obj i).property))
    exact ⟨⟨M, hM⟩, ⟨(fullyFaithfulDescentDataForget P f).preimageIso
      (e.app ⟨M, hM⟩ ≪≫ α)⟩⟩⟩
  exact { }

/-- A full subpseudofunctor of a stack cut out by a property that is closed under isomorphisms
and local for the covering sieves is a stack. -/
theorem isStack_fullsubcategory {J : GrothendieckTopology C} [F.IsStack J]
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ ⦃S : C⦄ (R : Sieve S), R ∈ J S → ∀ M : F.obj (.mk (op S)),
      (∀ ⦃Y : C⦄ (g : Y ⟶ S), R g → P.prop _ ((F.map g.op.toLoc).toFunctor.obj M)) →
        P.prop _ M) :
    P.fullsubcategory.IsStack J :=
  IsStack.of_isStackFor fun S R hR ↦ by
    have := (F.isStackFor' R hR).isEquivalence
    exact ⟨isEquivalence_toDescentData_fullsubcategory P
      (fun M hM ↦ hP R hR M (fun Y g hg ↦ hM ⟨Over.mk g, hg⟩))⟩

end CategoryTheory.Pseudofunctor.ObjectProperty

/-! ### Nested substacks: the ambient stack is `Q.fullsubcategory` for `P ≤ Q` -/

namespace CategoryTheory.Pseudofunctor.ObjectProperty

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

section Lift

variable (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

-- The objects of `P.fullsubcategory.obj _` (a `Cat.of`) must be seen as objects of `P.Obj _`.
set_option backward.isDefEq.respectTransparency false in
/-- A descent datum for `F` whose objects satisfy `P` is a descent datum for
`P.fullsubcategory`, with the same objects and morphisms. -/
def descentDataLift (D : F.DescentData f) (hD : ∀ i, P.prop _ (D.obj i)) :
    P.fullsubcategory.DescentData f where
  obj i := ⟨D.obj i, hD i⟩
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := ObjectProperty.homMk (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    apply InducedCategory.hom_ext
    exact (fullsubcategory_pullHom_hom P _ g gf₁ gf₂ hgf₁ hgf₂).trans
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  hom_self Y q i g hg := by
    apply InducedCategory.hom_ext
    exact D.hom_self q g hg
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply InducedCategory.hom_ext
    exact D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

end Lift

variable (P Q : F.ObjectProperty) [P.IsClosedUnderMapObj] [Q.IsClosedUnderMapObj]

-- As in `toDescentDataCompDescentDataForgetIso`, the objects of `P.fullsubcategory.obj _` (a
-- `Cat.of`) must be seen as objects of `P.Obj _`.
set_option backward.isDefEq.respectTransparency false in
/-- If `Q.fullsubcategory.toDescentData f` is an equivalence, `P ≤ Q`, and `P` is closed under
isomorphisms and local along `f` for objects satisfying `Q`, then
`P.fullsubcategory.toDescentData f` is an equivalence. -/
lemma isEquivalence_toDescentData_fullsubcategory_of_le [P.IsClosedUnderIsomorphisms]
    {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    [(Q.fullsubcategory.toDescentData f).IsEquivalence]
    (hPQ : ∀ X M, P.prop X M → Q.prop X M)
    (hP : ∀ M : F.obj (.mk (op S)), Q.prop _ M →
      (∀ i, P.prop _ ((F.map (f i).op.toLoc).toFunctor.obj M)) → P.prop _ M) :
    (P.fullsubcategory.toDescentData f).IsEquivalence := by
  let eP := toDescentDataCompDescentDataForgetIso P f
  let eQ := toDescentDataCompDescentDataForgetIso Q f
  have hle : P.prop (.mk (op S)) ≤ Q.prop (.mk (op S)) := fun M hM ↦ hPQ _ M hM
  have hQ : (Q.fullsubcategory.toDescentData f ⋙ descentDataForget Q f).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful _).comp (fullyFaithfulDescentDataForget Q f)
  have hF : ((P.prop (.mk (op S))).ι ⋙ F.toDescentData f).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulιOfLE hle).comp (hQ.ofIso eQ)).ofIso (Iso.refl _)
  have hff' := Functor.FullyFaithful.ofCompFaithful (G := descentDataForget P f) (hF.ofIso eP.symm)
  have := hff'.full
  have := hff'.faithful
  have : (P.fullsubcategory.toDescentData f).EssSurj := ⟨fun D ↦ by
    let D₀ := (descentDataForget P f).obj D
    let DQ := descentDataLift Q D₀ (fun i ↦ hPQ _ _ (D.obj i).property)
    let MQ := (Q.fullsubcategory.toDescentData f).objPreimage DQ
    let α : (Q.fullsubcategory.toDescentData f).obj MQ ≅ DQ :=
      (Q.fullsubcategory.toDescentData f).objObjPreimageIso DQ
    let β : (F.toDescentData f).obj MQ.obj ≅ D₀ :=
      (eQ.app MQ).symm ≪≫ (descentDataForget Q f).mapIso α ≪≫
        (Iso.refl _ : (descentDataForget Q f).obj DQ ≅ D₀)
    have hM : P.prop _ MQ.obj := hP MQ.obj MQ.property (fun i ↦
      (P.prop _).prop_of_iso
        { hom := β.inv.hom i
          inv := β.hom.hom i
          hom_inv_id := congrArg (fun φ ↦ DescentData.Hom.hom φ i) β.inv_hom_id
          inv_hom_id := congrArg (fun φ ↦ DescentData.Hom.hom φ i) β.hom_inv_id }
        (by exact (D.obj i).property))
    exact ⟨⟨MQ.obj, hM⟩, ⟨(fullyFaithfulDescentDataForget P f).preimageIso
      (eP.app ⟨MQ.obj, hM⟩ ≪≫ β)⟩⟩⟩
  exact { }

/-- **Nested substacks.** If `P ≤ Q`, `Q.fullsubcategory` is a stack for `J`, and `P` is closed
under isomorphisms and local for the covering sieves of `J` on objects satisfying `Q`, then
`P.fullsubcategory` is a stack for `J`. -/
theorem isStack_fullsubcategory_of_le {J : GrothendieckTopology C} [P.IsClosedUnderIsomorphisms]
    [Q.fullsubcategory.IsStack J] (hPQ : ∀ X M, P.prop X M → Q.prop X M)
    (hP : ∀ ⦃S : C⦄ (R : Sieve S), R ∈ J S → ∀ M : F.obj (.mk (op S)), Q.prop _ M →
      (∀ ⦃Y : C⦄ (g : Y ⟶ S), R g → P.prop _ ((F.map g.op.toLoc).toFunctor.obj M)) →
        P.prop _ M) :
    P.fullsubcategory.IsStack J :=
  IsStack.of_isStackFor fun S R hR ↦ by
    have := (Q.fullsubcategory.isStackFor' R hR).isEquivalence
    exact ⟨isEquivalence_toDescentData_fullsubcategory_of_le P Q hPQ
      (fun M hQM hM ↦ hP R hR M hQM (fun Y g hg ↦ hM ⟨Over.mk g, hg⟩))⟩

end CategoryTheory.Pseudofunctor.ObjectProperty
