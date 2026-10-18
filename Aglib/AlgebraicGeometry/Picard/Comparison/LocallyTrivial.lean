/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Injectivity
public import Aglib.CategoryTheory.Sites.Descent.OverForget
public import Aglib.CategoryTheory.Sites.Descent.Bind
public import Aglib.CategoryTheory.Adjunction.Unit
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack

/-!
# Fppf-locally trivial classes are base classes (Kleiman, Thm 2.5(1))

For `S` locally Noetherian and `p : X ⟶ S` proper, flat, with geometrically integral fibres,
every class on `X ×_S T` that vanishes fppf-locally on `T` is pulled back from `T`
(`fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral`); hence
`toFppfPicardSheaf p : P_{X/S} ⟶ Pic_{X/S,(fppf)}` is a monomorphism
(`mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral`). This is Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(1), p. 18, proved along
[Stacks 0B9M](https://stacks.math.columbia.edu/tag/0B9M), without flat base change.

The descent is organized on the site `Over S` with two pseudofunctors: line bundles on `T`
(`lineBundlePseudofunctor.restrictAlong (Over.forget S)`) and line bundles on `X ×_S T`
(`lineBundlePseudofunctor.restrictAlong (familyScheme p)`), related by the transformation
`familyPullback p` with components the pullbacks along `q_T : X ×_S T ⟶ T`
(`CompTrans.ofNatTrans` at `familyProjection p`).

* Universal O-connectedness makes `q_T^*` bijective on morphisms into trivial line bundles
  (`bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral`), through the
  adjunction unit
  (`isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`).
* The descent datum of a line bundle `L` on `X ×_S T` along a covering family over which `L` is
  trivial therefore lifts to a descent datum of line bundles on the base
  (`CompTrans.exists_descentData_iso_of_bijective`), which is effective
  (`isStack_lineBundlePseudofunctor_fppfTopology` with `isStackFor_restrictAlong_overForget`):
  this replaces the unit cocycle of Stacks 0B9M. The descended `N` satisfies `q_T^* N ≅ L` by
  full faithfulness of descent on `X ×_S T` (Stacks 023T for line bundles), transferred from the
  covering of `X ×_S T` by the `X ×_S U` through graph morphisms
  (`nonempty_iso_of_toDescentData_iso`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat
open Over (homMkFamily)

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

open Scheme.Modules Scheme.Modules.Invertible

variable {S X : Scheme.{u}} (p : X ⟶ S)

section Graph

variable {T : Over S} {W : Scheme.{u}} (h : W ⟶ pullback p T.hom)

/-- The `S`-scheme `W`, mapped to `T` by `h ≫ pr₂`. -/
abbrev graphBase : Over.mk ((h ≫ pullback.snd p T.hom) ≫ T.hom) ⟶ T :=
  Over.homMk (h ≫ pullback.snd p T.hom) rfl

/-- The graph `W ⟶ X ×_S W` of `h ≫ pr₁ : W ⟶ X`. -/
def graph : W ⟶ pullback p ((h ≫ pullback.snd p T.hom) ≫ T.hom) :=
  pullback.lift (h ≫ pullback.fst p T.hom) (𝟙 W) (by
    rw [Category.assoc, pullback.condition, Category.id_comp, Category.assoc])

@[reassoc (attr := simp)]
theorem graph_fst : graph p h ≫ pullback.fst _ _ = h ≫ pullback.fst p T.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd : graph p h ≫ pullback.snd _ _ = 𝟙 W :=
  pullback.lift_snd _ _ _

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.hom_ext` and the projection lemmas match them, as in
-- `familyScheme_map_fst`.
set_option backward.isDefEq.respectTransparency false in
/-- The graph followed by the map of fibre products induced by `k` is any morphism with the same
projections. -/
theorem graph_comp_familyScheme_map {V : Over S}
    (k : Over.mk ((h ≫ pullback.snd p T.hom) ≫ T.hom) ⟶ V) (h' : W ⟶ pullback p V.hom)
    (h₁ : h' ≫ pullback.fst p V.hom = h ≫ pullback.fst p T.hom)
    (h₂ : h' ≫ pullback.snd p V.hom = k.left) :
    graph p h ≫ (familyScheme p).map k = h' := by
  apply pullback.hom_ext
  · rw [Category.assoc, familyScheme_map_fst, h₁]
    exact graph_fst p h
  · rw [Category.assoc, familyScheme_map_snd, h₂]
    erw [graph_snd_assoc p h]

theorem graph_comp_familyScheme_map_graphBase :
    graph p h ≫ (familyScheme p).map (graphBase p h) = h :=
  graph_comp_familyScheme_map p h _ h rfl rfl

end Graph

section Prestack

variable {F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}}

variable {T : Over S} {ι : Type (u + 1)} {V : ι → Over S} (f : ∀ i, V i ⟶ T)

/-- The maps `X ×_S V i ⟶ X ×_S T` of a family `f i : V i ⟶ T`. -/
abbrev familyMap : ∀ i, (familyScheme p).obj (V i) ⟶ (familyScheme p).obj T :=
  fun i ↦ (familyScheme p).map (f i)

/-- The `S`-scheme `W` with `q : W ⟶ X ×_S T`, as an object of `Over S`. -/
abbrev graphObj {W : Scheme.{u}} (q : W ⟶ pullback p T.hom) : Over S :=
  Over.mk ((q ≫ pullback.snd p T.hom) ≫ T.hom)

-- As for `graph_comp_familyScheme_map`.
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `h : W ⟶ X ×_S V i` over `X ×_S T`, as a morphism of `S`-schemes
`W ⟶ V i`. -/
abbrev graphLift {W : Scheme.{u}} (q : W ⟶ pullback p T.hom) {i : ι}
    (h : W ⟶ pullback p (V i).hom) (hh : h ≫ (familyScheme p).map (f i) = q) :
    graphObj p q ⟶ V i :=
  Over.homMk (h ≫ pullback.snd p (V i).hom) (by
    change (h ≫ pullback.snd p (V i).hom) ≫ (V i).hom = (q ≫ pullback.snd p T.hom) ≫ T.hom
    have e₁ : pullback.snd p (V i).hom ≫ (V i).hom =
        pullback.snd p (V i).hom ≫ (f i).left ≫ T.hom := by rw [Over.w (f i)]
    rw [Category.assoc, e₁, ← familyScheme_map_snd_assoc, reassoc_of% hh, Category.assoc])

-- As for `graph_comp_familyScheme_map`.
set_option backward.isDefEq.respectTransparency false in
theorem graphLift_comp {W : Scheme.{u}} (q : W ⟶ pullback p T.hom) {i : ι}
    (h : W ⟶ pullback p (V i).hom) (hh : h ≫ (familyScheme p).map (f i) = q) :
    graphLift p f q h hh ≫ f i = graphBase p q := by
  ext
  change (h ≫ pullback.snd p (V i).hom) ≫ (f i).left = q ≫ pullback.snd p T.hom
  rw [← hh, Category.assoc, Category.assoc, familyScheme_map_snd]

-- As for `graph_comp_familyScheme_map`.
set_option backward.isDefEq.respectTransparency false in
theorem graph_comp_graphLift {W : Scheme.{u}} (q : W ⟶ pullback p T.hom) {i : ι}
    (h : W ⟶ pullback p (V i).hom) (hh : h ≫ (familyScheme p).map (f i) = q) :
    graph p q ≫ (familyScheme p).map (graphLift p f q h hh) = h :=
  graph_comp_familyScheme_map p q _ h (by
    rw [← hh, Category.assoc, familyScheme_map_fst]) rfl

-- As for Mathlib's `pullHom`: the objects of `F.obj _` (a `Cat.of`) must be seen as objects of the
-- underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- A morphism of descent data of objects for `F.restrictAlong (familyScheme p)` along `f` is a
morphism of descent data for `F` along the maps `X ×_S V i ⟶ X ×_S T`: the compatibility over a
scheme `W` over `X ×_S T` is the pullback, along the graph `W ⟶ X ×_S W`, of the compatibility
over the `S`-scheme `W`. -/
def descentHomOfFamily {A B : F.obj (.mk (op ((familyScheme p).obj T)))}
    (φ : ((F.restrictAlong (familyScheme p)).toDescentData f).obj A ⟶
      ((F.restrictAlong (familyScheme p)).toDescentData f).obj B) :
    (F.toDescentData (familyMap p f)).obj A ⟶ (F.toDescentData (familyMap p f)).obj B where
  hom := φ.hom
  comm W q i₁ i₂ h₁ h₂ hh₁ hh₂ := by
    refine (toDescentData_comm_iff F (familyMap p f) (φ.hom i₁) (φ.hom i₂) q h₁ h₂ hh₁ hh₂).2 ?_
    have hc := (toDescentData_comm_iff (F.restrictAlong (familyScheme p)) f (φ.hom i₁)
      (φ.hom i₂) (graphBase p q) (graphLift p f q h₁ hh₁) (graphLift p f q h₂ hh₂)
      (graphLift_comp p f q h₁ hh₁) (graphLift_comp p f q h₂ hh₂)).1
        (φ.comm (graphBase p q) (graphLift p f q h₁ hh₁) (graphLift p f q h₂ hh₂)
          (graphLift_comp p f q h₁ hh₁) (graphLift_comp p f q h₂ hh₂))
    rw [restrictAlong_pullHom', restrictAlong_pullHom'] at hc
    have hc' := congrArg (fun k ↦ pullHom k (graph p q) q q
      (graph_comp_familyScheme_map_graphBase p q) (graph_comp_familyScheme_map_graphBase p q)) hc
    simp only [pullHom_pullHom] at hc'
    rw [pullHom_congr_left _ (graph_comp_graphLift p f q h₁ hh₁) _ _ hh₁ hh₁,
      pullHom_congr_left _ (graph_comp_graphLift p f q h₂ hh₂) _ _ hh₂ hh₂] at hc'
    exact hc'

/-- **Full faithfulness of descent, transferred to `Over S`.** If `F` is an fppf prestack and the
maps `X ×_S V i ⟶ X ×_S T` generate an fppf covering sieve, then objects of
`F (X ×_S T)` with isomorphic descent data along `f` for
`F.restrictAlong (familyScheme p)` are isomorphic. -/
theorem nonempty_iso_of_toDescentData_iso [F.IsPrestack Scheme.fppfTopology]
    (hf : Sieve.ofArrows _ (familyMap p f) ∈ Scheme.fppfTopology ((familyScheme p).obj T))
    {A B : F.obj (.mk (op ((familyScheme p).obj T)))}
    (e : ((F.restrictAlong (familyScheme p)).toDescentData f).obj A ≅
      ((F.restrictAlong (familyScheme p)).toDescentData f).obj B) :
    Nonempty (A ≅ B) := by
  have hff := F.fullyFaithfulToDescentData (J := Scheme.fppfTopology) _ hf
  refine ⟨hff.preimageIso
    { hom := descentHomOfFamily p f e.hom
      inv := descentHomOfFamily p f e.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
  · ext i
    have h := congrArg (fun φ ↦ DescentData.Hom.hom φ i) e.hom_inv_id
    exact h
  · ext i
    have h := congrArg (fun φ ↦ DescentData.Hom.hom φ i) e.inv_hom_id
    exact h

end Prestack

/-- Line bundles on `T`, on the site `Over S`. -/
abbrev baseLineBundles (S : Scheme.{u}) : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  lineBundlePseudofunctor.restrictAlong (Over.forget S)

/-- Line bundles on `X ×_S T`, on the site `Over S`. -/
abbrev familyLineBundles : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  lineBundlePseudofunctor.restrictAlong (familyScheme p)

/-- Pullback of line bundles along the projections `q_T : X ×_S T ⟶ T`, as a transformation of
pseudofunctors on `Over S`. -/
def familyPullback : CompTrans (baseLineBundles S) (familyLineBundles p) :=
  CompTrans.ofNatTrans lineBundlePseudofunctor (familyProjection p)

/-- Trivial line bundles: objects isomorphic to the structure module. -/
def IsTrivialLineBundle {T : Over S} (N : (baseLineBundles S).obj (.mk (op T))) : Prop :=
  Nonempty (N.obj ≅ SheafOfModules.unit T.left.ringCatSheaf)

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different instance
-- paths, as in `isIso_unit_app_unit_of_isIso_c`.
set_option backward.isDefEq.respectTransparency false in
theorem isTrivialLineBundle_map {T T' : Over S} (g : T' ⟶ T)
    (N : (baseLineBundles S).obj (.mk (op T))) (hN : IsTrivialLineBundle N) :
    IsTrivialLineBundle (((baseLineBundles S).map g.op.toLoc).toFunctor.obj N) := by
  obtain ⟨e⟩ := hN
  exact ⟨(Scheme.Modules.pullback g.left).mapIso e ≪≫ pullbackUnitIso g.left⟩

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different instance
-- paths, as in `isIso_unit_app_unit_of_isIso_c`; the morphisms of the full subcategory are compared
-- through their underlying module morphisms.
set_option backward.isDefEq.respectTransparency false in
/-- **Universal O-connectedness on morphisms.** For `S` locally Noetherian and `p` proper, flat,
with geometrically integral fibres, pullback along `q_T` is bijective on morphisms of line bundles
with trivial target. -/
theorem bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p]
    [GeometricallyIntegral p] {T : Over S} (N N' : (baseLineBundles S).obj (.mk (op T)))
    (hN' : IsTrivialLineBundle N') :
    Function.Bijective (fun φ : N ⟶ N' ↦ ((familyPullback p).app T).map φ) := by
  obtain ⟨e⟩ := hN'
  have := isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p T.hom
  have : IsIso ((pullbackPushforwardAdjunction (pullback.snd p T.hom)).unit.app N'.obj) :=
    (NatTrans.isIso_app_iff_of_iso _ e.symm).mp inferInstance
  have hb := (pullbackPushforwardAdjunction (pullback.snd p T.hom)).bijective_map_of_isIso_unit_app
    N.obj N'.obj
  refine ⟨fun φ ψ h ↦ ObjectProperty.hom_ext _ (hb.1 (congrArg (fun k ↦ k.hom) h)),
    fun ψ ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hb.2 ψ.hom
  exact ⟨ObjectProperty.homMk φ, ObjectProperty.hom_ext _ hφ⟩

section Assembly

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets the projection lemmas match them, as in `familyScheme_map_fst`.
set_option backward.isDefEq.respectTransparency false in
/-- The maps `X ×_S U i ⟶ X ×_S T` of an fppf covering family `g i : U i ⟶ T.left` generate an fppf
covering sieve of `X ×_S T`: it contains the pullback of the sieve of `g` along `q_T`. -/
theorem ofArrows_familyMap_mem {T : Over S} {ι : Type (u + 1)} {U : ι → Scheme.{u}}
    (g : ∀ i, U i ⟶ T.left) (hg : Sieve.ofArrows U g ∈ Scheme.fppfTopology T.left) :
    Sieve.ofArrows _ (familyMap p (homMkFamily g)) ∈
      Scheme.fppfTopology ((familyScheme p).obj T) := by
  refine Scheme.fppfTopology.superset_covering ?_
    (Scheme.fppfTopology.pullback_stable (pullback.snd p T.hom) hg)
  rintro W h ⟨Z, k, _, ⟨i⟩, hk⟩
  have hc : (h ≫ pullback.fst p T.hom) ≫ p = k ≫ g i ≫ T.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hk, Category.assoc]
  refine ⟨_, pullback.lift (h ≫ pullback.fst p T.hom) k hc, _, Presieve.ofArrows.mk i, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, familyMap, familyScheme_map_fst]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, familyMap, familyScheme_map_snd]
    erw [pullback.lift_snd_assoc]
    exact hk

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different instance
-- paths, as in `isIso_unit_app_unit_of_isIso_c`.
set_option backward.isDefEq.respectTransparency false in
/-- **Descent of fppf-locally trivial line bundles** (Stacks 0B9M, second paragraph). For `S`
locally Noetherian and `p` proper, flat, with geometrically integral fibres, a line bundle `L` on
`X ×_S T` that is trivial on `X ×_S U i` for an fppf covering family `g i : U i ⟶ T.left` is
isomorphic to `q_T^* N` for a line bundle `N` on `T`. -/
theorem exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p]
    [GeometricallyIntegral p] {T : Over S} {ι : Type (u + 1)} {U : ι → Scheme.{u}}
    (g : ∀ i, U i ⟶ T.left) (hg : Sieve.ofArrows U g ∈ Scheme.fppfTopology T.left)
    (L : (familyLineBundles p).obj (.mk (op T)))
    (hL : ∀ i, Nonempty ((((familyLineBundles p).map (homMkFamily g i).op.toLoc).toFunctor.obj
      L).obj ≅ SheafOfModules.unit (pullback p (g i ≫ T.hom)).ringCatSheaf)) :
    ∃ N : (baseLineBundles S).obj (.mk (op T)),
      Nonempty (((familyPullback p).app T).obj N ≅ L) := by
  let D₂ := ((familyLineBundles p).toDescentData (homMkFamily g)).obj L
  let M : ∀ i, (baseLineBundles S).obj (.mk (op (Over.mk (g i ≫ T.hom)))) := fun i ↦
    ⟨(trivialLineBundle (U i)).val, (trivialLineBundle (U i)).property⟩
  have hM : ∀ i, IsTrivialLineBundle (M i) := fun i ↦
    ⟨coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit (U i).ringCatSheaf)⟩
  let e : ∀ i, ((familyPullback p).app _).obj (M i) ≅ D₂.obj i := fun i ↦
    ObjectProperty.isoMk _ ((Scheme.Modules.pullback (pullback.snd p (g i ≫ T.hom))).mapIso
        (coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit (U i).ringCatSheaf)) ≪≫
      pullbackUnitIso _ ≪≫ (hL i).some.symm)
  obtain ⟨D₁, ⟨eD⟩⟩ := (familyPullback p).exists_descentData_iso_of_bijective (homMkFamily g)
    (fun _ N ↦ IsTrivialLineBundle N) (fun _ _ g N hN ↦ isTrivialLineBundle_map g N hN)
    (fun _ N N' hN' ↦
      bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral p N N' hN')
    D₂ M hM e
  have hstack := isStackFor_restrictAlong_overForget (F := lineBundlePseudofunctor.{u}) (g := g)
    (lineBundlePseudofunctor.isStackFor (J := Scheme.fppfTopology) (Presieve.ofArrows U g) hg)
  rw [isStackFor_ofArrows_iff] at hstack
  let N := ((baseLineBundles S).toDescentData (homMkFamily g)).objPreimage D₁
  let eN := ((baseLineBundles S).toDescentData (homMkFamily g)).objObjPreimageIso D₁
  let eT : ((familyLineBundles p).toDescentData (homMkFamily g)).obj
      (((familyPullback p).app T).obj N) ≅
        ((familyLineBundles p).toDescentData (homMkFamily g)).obj L :=
    ((familyPullback p).toDescentDataIso (homMkFamily g)).symm.app N ≪≫
      ((familyPullback p).descentData (homMkFamily g)).mapIso eN ≪≫ eD
  exact ⟨N, nonempty_iso_of_toDescentData_iso p (homMkFamily g) (ofArrows_familyMap_mem p g hg) eT⟩

-- `T.Modules` and `SheafOfModules T.ringCatSheaf` are the same category under different instance
-- paths, as in `isIso_unit_app_unit_of_isIso_c`.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Thm 2.5(1), descent premise** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5(1), p. 18; [Stacks 0B9M](https://stacks.math.columbia.edu/tag/0B9M)).
For `S` locally Noetherian and `p` proper, flat, with geometrically integral fibres, every class on
`X ×_S T` that vanishes on an fppf covering sieve of `T` is pulled back from `T`. -/
theorem fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    FppfLocallyTrivialMemBaseImage p := by
  intro T a ha
  induction a using Quotient.inductionOn with | h L =>
  rw [GrothendieckTopology.mem_over_iff] at ha
  let R := Sieve.overEquiv T.unop
    (Presheaf.equalizerSieve (F := familyPicardFunctor p) (Quotient.mk _ L) 0)
  let g : ∀ a : R.arrows.category, a.obj.left ⟶ T.unop.left := fun a ↦ a.obj.hom
  have hg : Sieve.ofArrows _ g ∈ Scheme.fppfTopology T.unop.left := by
    rw [Sieve.ofArrows_category', Sieve.generate_sieve]
    exact ha
  have hL : ∀ a, Nonempty ((((familyLineBundles p).map (homMkFamily g a).op.toLoc).toFunctor.obj
      (⟨L.val, L.property⟩ : (familyLineBundles p).obj (.mk (op T.unop)))).obj ≅
        SheafOfModules.unit (pullback p (g a ≫ T.unop.hom)).ringCatSheaf) := by
    intro a
    have h := (Sieve.overEquiv_iff _ a.obj.hom).mp a.property
    have h' : classOf _ (pullbackLineBundle ((familyScheme p).map (homMkFamily g a)) L) =
        classOf _ (trivialLineBundle _) := by
      have h₀ : ((familyPicardFunctor p).map (homMkFamily g a).op).hom (Quotient.mk _ L) =
          ((familyPicardFunctor p).map (homMkFamily g a).op).hom 0 := h
      rw [map_zero] at h₀
      exact h₀
    obtain ⟨e⟩ := (class_eq_iff _ _ _).mp h'
    exact ⟨e ≪≫ coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
      SheafOfModules.unit (pullback p (g a ≫ T.unop.hom)).ringCatSheaf)⟩
  obtain ⟨N, ⟨e⟩⟩ := exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral p g hg
    ⟨L.val, L.property⟩ hL
  refine ⟨classOf T.unop.left ⟨N.obj, N.property⟩, ?_⟩
  exact (basePullback_app_apply p T _).trans
    ((pullbackClass_classOf _ _).trans
      (Quotient.sound ⟨(CategoryTheory.ObjectProperty.ι _).mapIso e⟩))

/-- **Kleiman, Thm 2.5(1)** (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(1),
p. 18). For `S` locally Noetherian and `p` proper, flat, with geometrically integral fibres,
`P_{X/S} ⟶ Pic_{X/S,(fppf)}` is injective on every `S`-scheme `T`. -/
theorem toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] (T : (Over S)ᵒᵖ) :
    Function.Injective ((toFppfPicardSheaf p).app T).hom :=
  toFppfPicardSheaf_app_injective_of_fppfLocallyTrivialMemBaseImage p
    (fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral p) T

/-- **Kleiman, Thm 2.5(1)**, monomorphism form. -/
theorem mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Mono (toFppfPicardSheaf p) :=
  mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage p
    (fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral p)

end Assembly

end AlgebraicGeometry.Scheme.RelativePicard
