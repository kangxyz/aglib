/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Gluing
public import Aglib.AlgebraicGeometry.Descent.Modules.Substack
public import Aglib.CategoryTheory.Sites.Descent.Rigidification

/-!
# Gluing rigidified pairs (Stacks 0B9N)

Let `p : X ⟶ S` have a section `o`. The gluing step of
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N) (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5(2), p. 18): rigidified pairs `P i` over the members `V i ⟶ T` of a
covering family whose pullbacks to every `Y` over two members are isomorphic glue to a line bundle
on `X ×_S T`. The isomorphisms of pairs are unique (Lemma 2.10), so they form a descent datum.

* `RigidifiedPair.map_rigidification_hom_eq_pullRig`: the rigidification of a pulled-back pair is
  `CompTrans.pullRig` (`CategoryTheory/Sites/Descent/Rigidification.lean`) at the origin pullback
  `originPullback p o ho`, with `E Y = O_Y` and `e y = pullbackUnitIso y.left`.
* `RigidifiedPair.PairCompat`: compatibility of a morphism `y₁^* L₁ ⟶ y₂^* L₂`, typed for the
  pullback pseudofunctor, with the rigidifications (`CompTrans.RigCompat`);
  `RigidifiedPair.Iso.pairCompat`, `RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c` (Lemma 2.10
  for such morphisms) and `RigidifiedPair.pairCompat_pullHom` (from
  `CompTrans.rigCompat_pullHom`). This is the pullback coherence of rigidified pairs, stated
  without the composite objects of `mapComp'`.
* `gluingDescentData`: the descent datum for `familyLineBundles p` of compatible pairs, when
  `O_Y ⟶ (X ×_S Y ⟶ Y)_* O` is an isomorphism for every `S`-scheme `Y`.
* `familyDescentData`: a descent datum for `F.restrictAlong (familyScheme p)` along `f` is a
  descent datum for `F` along the maps `X ×_S V i ⟶ X ×_S T` (through graph morphisms, as in
  `descentHomOfFamily`); `exists_iso_of_familyDescentData` makes it effective for a stack.
* `exists_lineBundle_of_rigidifiedPairs_of_isIso_c`: the glued line bundle.

The pulled-back bundles have two presentations: Mathlib's pullback functors in
`RigidifiedPair.map`, and the pullback pseudofunctor in descent data. They are compared only in
`RigidifiedPair.Iso.pairCompat` and `RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c`, through
`CompEq`, so that the kernel compares the morphisms and objects rather than unfolding the
composites. Measured on development versions of this file: an equation of composites stated in one
presentation and used in the other cost the kernel 7 to 16 s per declaration; through `CompEq` the
kernel check of every declaration stays below the 100 ms profiler threshold (elaboration of
`gluingDescentData` takes about 2.3 s), and the module builds in about 7.5 s.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat
open Over (homMkFamily)

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The structure module `O_Y`, as an object of the base pseudofunctor
`pullbackPseudofunctor.restrictAlong (Over.forget S)`. -/
abbrev baseUnit (Y : Over S) :
    (pullbackPseudofunctor.restrictAlong (Over.forget S)).obj (.mk (op Y)) :=
  SheafOfModules.unit Y.left.ringCatSheaf

/-- The isomorphisms `y^* O_V ⟶ O_Y` (`pullbackUnitIso`), typed for the base pseudofunctor. -/
abbrev baseUnitHom ⦃V Y : Over S⦄ (y : Y ⟶ V) :
    ((pullbackPseudofunctor.restrictAlong (Over.forget S)).map y.op.toLoc).toFunctor.obj
      (baseUnit V) ⟶ baseUnit Y :=
  (pullbackUnitIso y.left).hom

-- As for `mapComp'_unit_pullbackUnitIso`.
set_option backward.isDefEq.respectTransparency false in
theorem baseUnitHom_comp ⦃V Y Y' : Over S⦄ (y : Y ⟶ V) (g : Y' ⟶ Y) :
    ((pullbackPseudofunctor.restrictAlong (Over.forget S)).mapComp' y.op.toLoc g.op.toLoc
        (g ≫ y).op.toLoc rfl).hom.toNatTrans.app (baseUnit V) ≫
      ((pullbackPseudofunctor.restrictAlong (Over.forget S)).map g.op.toLoc).toFunctor.map
        (baseUnitHom y) ≫ baseUnitHom g = baseUnitHom (g ≫ y) :=
  mapComp'_unit_pullbackUnitIso y g

namespace RigidifiedPair

variable {p o ho}

-- Objects of the pullback pseudofunctor's categories are matched with `X.Modules` up to instance
-- transparency, as in `pullbackPseudofunctor_square_app`.
set_option backward.isDefEq.respectTransparency false in
/-- The rigidification of a pulled-back pair is `CompTrans.pullRig` at the origin pullback. -/
theorem map_rigidification_hom_eq_pullRig {V Y : Over S} (y : Y ⟶ V)
    (P : RigidifiedPair p o ho V) :
    (RigidifiedPair.map y P).rigidification.hom =
      (originPullback p o ho).pullRig baseUnit baseUnitHom y P.rigidification.hom :=
  map_rigidification_hom p o ho y P

/-- Compatibility of a morphism `φ : y₁^* L₁ ⟶ y₂^* L₂`, typed for the pullback pseudofunctor
`pullbackPseudofunctor.restrictAlong (familyScheme p)`, with the rigidifications of the pulled-back
pairs: `CompTrans.RigCompat` at the origin pullback (the condition `RigidifiedPair.Iso.comm`, with
both rigidifications written through `CompTrans.pullRig`). -/
abbrev PairCompat {V₁ V₂ Y : Over S} (y₁ : Y ⟶ V₁) (y₂ : Y ⟶ V₂) (P₁ : RigidifiedPair p o ho V₁)
    (P₂ : RigidifiedPair p o ho V₂)
    (φ : ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₁.op.toLoc).toFunctor.obj
        P₁.bundle.val ⟶
      ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₂.op.toLoc).toFunctor.obj
        P₂.bundle.val) : Prop :=
  (originPullback p o ho).RigCompat baseUnit baseUnitHom y₁ y₂ P₁.rigidification.hom
    P₂.rigidification.hom φ

-- Objects of the pullback pseudofunctor's categories are matched with `X.Modules` up to instance
-- transparency, as in `pullbackPseudofunctor_square_app`.
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of pulled-back pairs satisfies `PairCompat`. -/
theorem Iso.pairCompat {V₁ V₂ Y : Over S} {y₁ : Y ⟶ V₁} {y₂ : Y ⟶ V₂}
    {P₁ : RigidifiedPair p o ho V₁} {P₂ : RigidifiedPair p o ho V₂}
    (ψ : RigidifiedPair.Iso (RigidifiedPair.map y₁ P₁) (RigidifiedPair.map y₂ P₂)) :
    PairCompat y₁ y₂ P₁ P₂ ψ.iso.hom := by
  have h : CompEq ((Scheme.Modules.pullback (originSection p o ho Y)).map ψ.iso.hom)
      (RigidifiedPair.map y₂ P₂).rigidification.hom
      (RigidifiedPair.map y₁ P₁).rigidification.hom := ψ.comm
  rw [map_rigidification_hom_eq_pullRig y₂ P₂, map_rigidification_hom_eq_pullRig y₁ P₁] at h
  exact h

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Lemma 2.10, for morphisms.** If `O_T ⟶ (X ×_S T ⟶ T)_* O` is an isomorphism, a
morphism of line bundles compatible with the rigidifications of two isomorphic pairs is the
isomorphism of pairs (the proof of `RigidifiedPair.Iso.eq_of_isIso_c`, which does not use that the
first morphism is invertible). -/
theorem Iso.hom_eq_of_comm_of_isIso_c {T : Over S} [IsIso (pullback.snd p T.hom).c]
    {P Q : RigidifiedPair p o ho T} (ψ : RigidifiedPair.Iso P Q)
    (φ : (P.bundle.val : (pullback p T.hom).Modules) ⟶ Q.bundle.val)
    (hφ : (Scheme.Modules.pullback (originSection p o ho T)).map φ ≫ Q.rigidification.hom =
      P.rigidification.hom) :
    φ = ψ.iso.hom := by
  obtain ⟨r, hr⟩ := exists_eq_globalScalarEndomorphism_of_isLocallyRankOne P.bundle.property
    (φ ≫ ψ.iso.inv)
  have hbij : Function.Bijective (pullback.snd p T.hom).appTop :=
    ConcreteCategory.bijective_of_isIso ((pullback.snd p T.hom).c.app (op ⊤))
  obtain ⟨w, rfl⟩ := hbij.2 r
  have h1 : (Scheme.Modules.pullback (originSection p o ho T)).map (φ ≫ ψ.iso.inv) = 𝟙 _ := by
    have h : (Scheme.Modules.pullback (originSection p o ho T)).map φ =
        (Scheme.Modules.pullback (originSection p o ho T)).map ψ.iso.hom := by
      rw [← cancel_mono Q.rigidification.hom, hφ, ψ.comm]
    rw [CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp,
      CategoryTheory.Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [hr, pullback_map_globalScalarEndomorphism, RigidifiedPair.originSection_appTop_snd_appTop]
    at h1
  have hw : w = 1 := globalScalarEndomorphism_injective_of_iso P.rigidification
    (h1.trans (globalScalarEndomorphism_one _).symm)
  subst hw
  rw [map_one, globalScalarEndomorphism_one] at hr
  rw [← cancel_mono ψ.iso.inv, hr, CategoryTheory.Iso.hom_inv_id]

-- Objects of the pullback pseudofunctor's categories are matched with `X.Modules` up to instance
-- transparency, as in `pullbackPseudofunctor_square_app`.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Lemma 2.10**, for morphisms satisfying `PairCompat`: if `O_Y ⟶ (X ×_S Y ⟶ Y)_* O`
is an isomorphism, such a morphism is the isomorphism of the pulled-back pairs. -/
theorem hom_eq_of_pairCompat_of_isIso_c {V₁ V₂ Y : Over S} [IsIso (pullback.snd p Y.hom).c]
    {y₁ : Y ⟶ V₁} {y₂ : Y ⟶ V₂} {P₁ : RigidifiedPair p o ho V₁} {P₂ : RigidifiedPair p o ho V₂}
    (ψ : RigidifiedPair.Iso (RigidifiedPair.map y₁ P₁) (RigidifiedPair.map y₂ P₂))
    (φ : ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₁.op.toLoc).toFunctor.obj
        P₁.bundle.val ⟶
      ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₂.op.toLoc).toFunctor.obj
        P₂.bundle.val)
    (hφ : PairCompat y₁ y₂ P₁ P₂ φ) : φ = ψ.iso.hom := by
  refine Iso.hom_eq_of_comm_of_isIso_c ψ φ ?_
  have h : CompEq ((Scheme.Modules.pullback (originSection p o ho Y)).map φ)
      ((originPullback p o ho).pullRig baseUnit baseUnitHom y₂ P₂.rigidification.hom)
      ((originPullback p o ho).pullRig baseUnit baseUnitHom y₁ P₁.rigidification.hom) := hφ
  rw [← map_rigidification_hom_eq_pullRig y₂ P₂, ← map_rigidification_hom_eq_pullRig y₁ P₁] at h
  exact h

/-- `PairCompat` is stable under `pullHom` (the pullback coherence of rigidified pairs). -/
theorem pairCompat_pullHom {V₁ V₂ Y Y' : Over S} {y₁ : Y ⟶ V₁} {y₂ : Y ⟶ V₂}
    {P₁ : RigidifiedPair p o ho V₁} {P₂ : RigidifiedPair p o ho V₂}
    {φ : ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₁.op.toLoc).toFunctor.obj
        P₁.bundle.val ⟶
      ((pullbackPseudofunctor.restrictAlong (familyScheme p)).map y₂.op.toLoc).toFunctor.obj
        P₂.bundle.val}
    (hφ : PairCompat y₁ y₂ P₁ P₂ φ) (g : Y' ⟶ Y) (gy₁ : Y' ⟶ V₁) (gy₂ : Y' ⟶ V₂)
    (h₁ : g ≫ y₁ = gy₁) (h₂ : g ≫ y₂ = gy₂) :
    PairCompat gy₁ gy₂ P₁ P₂ (pullHom φ g gy₁ gy₂ h₁ h₂) :=
  CompTrans.rigCompat_pullHom (fun _ _ _ y g ↦ baseUnitHom_comp y g) hφ g gy₁ gy₂ h₁ h₂

end RigidifiedPair

-- `familyLineBundles p` is a full subpseudofunctor restricted along `familyScheme p`.
set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` for `familyLineBundles p` is `pullHom` for the pullback pseudofunctor restricted
along `familyScheme p`, on underlying module morphisms. -/
theorem familyLineBundles_pullHom_hom ⦃V₁ V₂ : Over S⦄
    ⦃M₁ : (familyLineBundles p).obj (.mk (op V₁))⦄ ⦃M₂ : (familyLineBundles p).obj (.mk (op V₂))⦄
    ⦃Y : Over S⦄ ⦃f₁ : Y ⟶ V₁⦄ ⦃f₂ : Y ⟶ V₂⦄
    (φ : ((familyLineBundles p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((familyLineBundles p).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : Over S⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ V₁) (gf₂ : Y' ⟶ V₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (pullHom (F := familyLineBundles p) φ g gf₁ gf₂ h₁ h₂).hom =
      pullHom (F := pullbackPseudofunctor.restrictAlong (familyScheme p)) (M₁ := M₁.obj)
        (M₂ := M₂.obj) φ.hom g gf₁ gf₂ h₁ h₂ :=
  (congrArg InducedCategory.Hom.hom (restrictAlong_pullHom (F := lineBundlePseudofunctor)
    (G := familyScheme p) φ g gf₁ gf₂ h₁ h₂)).trans
      ((ObjectProperty.fullsubcategory_pullHom_hom _ _ _ _ _ _ _).trans
        (restrictAlong_pullHom (F := pullbackPseudofunctor) (G := familyScheme p)
          (M₁ := M₁.obj) (M₂ := M₂.obj) φ.hom g gf₁ gf₂ h₁ h₂).symm)

section Datum

variable (hc : ∀ Y : Over S, IsIso (pullback.snd p Y.hom).c)
  {T : Over S} {ι : Type (u + 1)} {V : ι → Over S} (f : ∀ i, V i ⟶ T)
  (P : ∀ i, RigidifiedPair p o ho (V i))
  (hP : ∀ ⦃Y : Over S⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (y₁ : Y ⟶ V i₁) (y₂ : Y ⟶ V i₂),
    y₁ ≫ f i₁ = q → y₂ ≫ f i₂ = q →
      Nonempty (RigidifiedPair.Iso (RigidifiedPair.map y₁ (P i₁)) (RigidifiedPair.map y₂ (P i₂))))

-- Objects of the pullback pseudofunctor's categories are matched with `X.Modules` up to instance
-- transparency, as in `pullbackPseudofunctor_square_app`; the morphisms of the full subcategory are
-- compared through their underlying module morphisms.
set_option backward.isDefEq.respectTransparency false in
/-- **The descent datum of compatible rigidified pairs** (Stacks 0B9N). The bundles of pairs
`P i` over `V i` that become isomorphic over every `Y` mapping to two of them form a descent
datum for `familyLineBundles p`, whose morphisms are the isomorphisms of pairs. These are unique
when `O_Y ⟶ (X ×_S Y ⟶ Y)_* O` is an isomorphism for every `S`-scheme `Y` (Lemma 2.10,
`RigidifiedPair.Iso.eq_of_isIso_c`): uniqueness gives the cocycle condition, and
`RigidifiedPair.pairCompat_pullHom` the compatibility with pullback. -/
def gluingDescentData : (familyLineBundles p).DescentData f where
  obj i := ⟨(P i).bundle.val, (P i).bundle.property⟩
  hom Y q i₁ i₂ y₁ y₂ hy₁ hy₂ := ObjectProperty.homMk (hP q y₁ y₂ hy₁ hy₂).some.iso.hom
  pullHom_hom Y' Y g q q' hq i₁ i₂ y₁ y₂ hy₁ hy₂ gy₁ gy₂ hgy₁ hgy₂ := by
    have := hc Y'
    apply ObjectProperty.hom_ext
    rw [familyLineBundles_pullHom_hom]
    exact RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c _ _
      (RigidifiedPair.pairCompat_pullHom (RigidifiedPair.Iso.pairCompat _) g gy₁ gy₂ hgy₁ hgy₂)
  hom_self Y q i y hy := by
    have := hc Y
    apply ObjectProperty.hom_ext
    rw [RigidifiedPair.Iso.eq_of_isIso_c p o ho (hP q y y hy hy).some (RigidifiedPair.Iso.refl _)]
    rfl
  hom_comp Y q i₁ i₂ i₃ y₁ y₂ y₃ hy₁ hy₂ hy₃ := by
    have := hc Y
    apply ObjectProperty.hom_ext
    have e := RigidifiedPair.Iso.eq_of_isIso_c p o ho
      ((hP q y₁ y₂ hy₁ hy₂).some.trans (hP q y₂ y₃ hy₂ hy₃).some) (hP q y₁ y₃ hy₁ hy₃).some
    exact congrArg (fun φ ↦ φ.iso.hom) e

end Datum

section GraphMap

variable {T : Over S} {W W' : Scheme.{u}} (q : W ⟶ pullback p T.hom) (q' : W' ⟶ pullback p T.hom)
  (w : W' ⟶ W) (hq : w ≫ q = q')

/-- A morphism `w : W' ⟶ W` over `X ×_S T`, as a morphism of the `S`-schemes `graphObj`. -/
abbrev graphMap : graphObj p q' ⟶ graphObj p q :=
  Over.homMk w (by
    change w ≫ (q ≫ pullback.snd p T.hom) ≫ T.hom = (q' ≫ pullback.snd p T.hom) ≫ T.hom
    rw [← hq]
    simp only [Category.assoc])

theorem graphMap_comp_graphBase : graphMap p q q' w hq ≫ graphBase p q = graphBase p q' := by
  ext
  change w ≫ q ≫ pullback.snd p T.hom = q' ≫ pullback.snd p T.hom
  rw [← hq, Category.assoc]

theorem graphMap_comp_graphLift {ι : Type (u + 1)} {V : ι → Over S} (f : ∀ i, V i ⟶ T) {i : ι}
    (h : W ⟶ pullback p (V i).hom) (hh : h ≫ (familyScheme p).map (f i) = q)
    (wh : W' ⟶ pullback p (V i).hom) (hwh : w ≫ h = wh)
    (hh' : wh ≫ (familyScheme p).map (f i) = q') :
    graphMap p q q' w hq ≫ graphLift p f q h hh = graphLift p f q' wh hh' := by
  ext
  change w ≫ h ≫ pullback.snd p (V i).hom = wh ≫ pullback.snd p (V i).hom
  rw [← hwh, Category.assoc]

theorem graph_comp_familyScheme_map_graphMap :
    graph p q' ≫ (familyScheme p).map (graphMap p q q' w hq) = w ≫ graph p q := by
  refine graph_comp_familyScheme_map p q' (graphMap p q q' w hq) (w ≫ graph p q) ?_ ?_
  · simp only [graphObj, Over.mk_hom, Category.assoc, graph_fst]
    rw [← Category.assoc, hq]
  · simp only [graphObj, Over.mk_hom, Category.assoc, graph_snd, Category.comp_id,
      Over.homMk_left]

end GraphMap

section FamilyTransfer

variable {F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}} {T : Over S} {ι : Type (u + 1)}
  {V : ι → Over S} {f : ∀ i, V i ⟶ T}

/-- The morphism over `q : W ⟶ X ×_S T` of `familyDescentData`: the pullback along the graph
`W ⟶ X ×_S W` of the morphism of `D` over the `S`-scheme `W`. -/
abbrev familyDescentHom (D : (F.restrictAlong (familyScheme p)).DescentData f) {W : Scheme.{u}}
    (q : W ⟶ (familyScheme p).obj T) {i₁ i₂ : ι} (h₁ : W ⟶ (familyScheme p).obj (V i₁))
    (h₂ : W ⟶ (familyScheme p).obj (V i₂)) (hh₁ : h₁ ≫ familyMap p f i₁ = q)
    (hh₂ : h₂ ≫ familyMap p f i₂ = q) :
    (F.map h₁.op.toLoc).toFunctor.obj (D.obj i₁) ⟶ (F.map h₂.op.toLoc).toFunctor.obj (D.obj i₂) :=
  pullHom (F := F) (f₁ := (familyScheme p).map (graphLift p f q h₁ hh₁))
    (f₂ := (familyScheme p).map (graphLift p f q h₂ hh₂))
    (D.hom (graphBase p q) (graphLift p f q h₁ hh₁) (graphLift p f q h₂ hh₂)
      (graphLift_comp p f q h₁ hh₁) (graphLift_comp p f q h₂ hh₂))
    (graph p q) h₁ h₂ (graph_comp_graphLift p f q h₁ hh₁) (graph_comp_graphLift p f q h₂ hh₂)

-- As for `descentHomOfFamily`.
set_option backward.isDefEq.respectTransparency false in
theorem familyDescentHom_pullHom (D : (F.restrictAlong (familyScheme p)).DescentData f)
    {W W' : Scheme.{u}} (w : W' ⟶ W) (q : W ⟶ (familyScheme p).obj T)
    (q' : W' ⟶ (familyScheme p).obj T) (hq : w ≫ q = q') {i₁ i₂ : ι}
    (h₁ : W ⟶ (familyScheme p).obj (V i₁)) (h₂ : W ⟶ (familyScheme p).obj (V i₂))
    (hh₁ : h₁ ≫ familyMap p f i₁ = q) (hh₂ : h₂ ≫ familyMap p f i₂ = q)
    (wh₁ : W' ⟶ (familyScheme p).obj (V i₁)) (wh₂ : W' ⟶ (familyScheme p).obj (V i₂))
    (hwh₁ : w ≫ h₁ = wh₁) (hwh₂ : w ≫ h₂ = wh₂) (hh₁' : wh₁ ≫ familyMap p f i₁ = q')
    (hh₂' : wh₂ ≫ familyMap p f i₂ = q') :
    pullHom (familyDescentHom p D q h₁ h₂ hh₁ hh₂) w wh₁ wh₂ hwh₁ hwh₂ =
      familyDescentHom p D q' wh₁ wh₂ hh₁' hh₂' := by
  have hD := D.pullHom_hom (graphMap p q q' w hq) (graphBase p q) (graphBase p q')
    (graphMap_comp_graphBase p q q' w hq) (graphLift p f q h₁ hh₁) (graphLift p f q h₂ hh₂)
    (graphLift_comp p f q h₁ hh₁) (graphLift_comp p f q h₂ hh₂) (graphLift p f q' wh₁ hh₁')
    (graphLift p f q' wh₂ hh₂') (graphMap_comp_graphLift p q q' w hq f h₁ hh₁ wh₁ hwh₁ hh₁')
    (graphMap_comp_graphLift p q q' w hq f h₂ hh₂ wh₂ hwh₂ hh₂')
  rw [restrictAlong_pullHom] at hD
  simp only [familyDescentHom]
  rw [← hD, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (graph_comp_familyScheme_map_graphMap p q q' w hq).symm _ _ _ _

-- As for `descentHomOfFamily`.
set_option backward.isDefEq.respectTransparency false in
/-- **Descent data over `Over S`, transferred to the family.** A descent datum for
`F.restrictAlong (familyScheme p)` along `f` gives a descent datum for `F` along the maps
`X ×_S V i ⟶ X ×_S T`, with the same objects: over a scheme `W` with `q : W ⟶ X ×_S T`, pull the
morphism of `D` over the `S`-scheme `W` back along the graph `W ⟶ X ×_S W`. -/
def familyDescentData (D : (F.restrictAlong (familyScheme p)).DescentData f) :
    F.DescentData (familyMap p f) where
  obj := D.obj
  hom W q i₁ i₂ h₁ h₂ hh₁ hh₂ := familyDescentHom p D q h₁ h₂ hh₁ hh₂
  pullHom_hom W' W w q q' hq i₁ i₂ h₁ h₂ hh₁ hh₂ wh₁ wh₂ hwh₁ hwh₂ :=
    familyDescentHom_pullHom p D w q q' hq h₁ h₂ hh₁ hh₂ wh₁ wh₂ hwh₁ hwh₂
      (by rw [← hwh₁, Category.assoc, hh₁, hq]) (by rw [← hwh₂, Category.assoc, hh₂, hq])
  hom_self W q i h hh := by
    change familyDescentHom p D q h h hh hh = 𝟙 _
    simp only [familyDescentHom]
    rw [D.hom_self _ _ (graphLift_comp p f q h hh)]
    exact pullHom_id' (F := F) _ _ _
  hom_comp W q i₁ i₂ i₃ h₁ h₂ h₃ hh₁ hh₂ hh₃ := by
    simp only [familyDescentHom]
    rw [← pullHom_comp, D.hom_comp]

/-- **Effective descent along the family.** If `F` is an fppf stack and the maps
`X ×_S V i ⟶ X ×_S T` generate an fppf covering sieve, a descent datum for
`F.restrictAlong (familyScheme p)` along `f` is effective on objects: some object of
`F (X ×_S T)` pulls back to its objects. -/
theorem exists_iso_of_familyDescentData [F.IsStack Scheme.fppfTopology]
    (hf : Sieve.ofArrows _ (familyMap p f) ∈ Scheme.fppfTopology ((familyScheme p).obj T))
    (D : (F.restrictAlong (familyScheme p)).DescentData f) :
    ∃ L : F.obj (.mk (op ((familyScheme p).obj T))),
      ∀ i, Nonempty ((F.map (familyMap p f i).op.toLoc).toFunctor.obj L ≅ D.obj i) := by
  have := F.isEquivalence_toDescentData (familyMap p f) hf
  let e := (F.toDescentData (familyMap p f)).objObjPreimageIso (familyDescentData p D)
  exact ⟨_, fun i ↦ ⟨⟨e.hom.hom i, e.inv.hom i,
    congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i) e.hom_inv_id,
    congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i) e.inv_hom_id⟩⟩⟩

end FamilyTransfer

-- As for `exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral`.
set_option backward.isDefEq.respectTransparency false in
/-- **Gluing compatible rigidified pairs** (Stacks 0B9N). If `O_Y ⟶ (X ×_S Y ⟶ Y)_* O` is an
isomorphism for every `S`-scheme `Y`, rigidified pairs `P i` over the members of an fppf covering
family `g i : U i ⟶ T.left` whose pullbacks to every `S`-scheme over two members are isomorphic
come from a line bundle `L` on `X ×_S T`: `X_{g i}^* L ≅ (P i).bundle`. -/
theorem exists_lineBundle_of_rigidifiedPairs_of_isIso_c
    (hc : ∀ Y : Over S, IsIso (pullback.snd p Y.hom).c) {T : Over S} {ι : Type (u + 1)}
    {U : ι → Scheme.{u}}
    (g : ∀ i, U i ⟶ T.left) (hg : Sieve.ofArrows U g ∈ Scheme.fppfTopology T.left)
    (P : ∀ i, RigidifiedPair p o ho (Over.mk (g i ≫ T.hom)))
    (hP : ∀ ⦃Y : Over S⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (y₁ : Y ⟶ Over.mk (g i₁ ≫ T.hom))
      (y₂ : Y ⟶ Over.mk (g i₂ ≫ T.hom)), y₁ ≫ homMkFamily g i₁ = q → y₂ ≫ homMkFamily g i₂ = q →
        Nonempty (RigidifiedPair.Iso (RigidifiedPair.map y₁ (P i₁))
          (RigidifiedPair.map y₂ (P i₂)))) :
    ∃ L : LineBundle (pullback p T.hom), ∀ i,
      Nonempty ((Scheme.Modules.pullback ((familyScheme p).map (homMkFamily g i))).obj L.val ≅
        (P i).bundle.val) := by
  obtain ⟨L, hL⟩ := exists_iso_of_familyDescentData p (F := lineBundlePseudofunctor)
    (ofArrows_familyMap_mem p g hg) (gluingDescentData p o ho hc (homMkFamily g) P hP)
  exact ⟨⟨L.obj, L.property⟩, fun i ↦ ⟨(CategoryTheory.ObjectProperty.ι _).mapIso (hL i).some⟩⟩

end AlgebraicGeometry.Scheme.RelativePicard
