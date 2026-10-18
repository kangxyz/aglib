/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.SiteChange

/-!
# Descent over `Over S₀` through the forgetful functor

For a family `g i : U i ⟶ T.left` with `T : Over S₀`, the morphisms
`Over.homMkFamily g i = Over.homMk (g i) : Over.mk (g i ≫ T.hom) ⟶ T` form the corresponding
family of `Over S₀`. Descent data for `F.restrictAlong (Over.forget S₀)` relative to it are descent
data for `F` relative to `g` (`Pseudofunctor.DescentData.ofOver`, a fully faithful functor
`DescentData.ofOverFunctor`), compatibly with `toDescentData`
(`DescentData.toDescentDataOfOverIso`). Hence, if `F` is a stack for the presieve of `g`, then
`F.restrictAlong (Over.forget S₀)` is a stack for the presieve of `Over.homMkFamily g`
(`isStackFor_restrictAlong_overForget`). This is the converse direction of
`isStackFor_ofArrows_map_of_restrictAlong` (`SiteChange.lean`).

The helpers `Over.homMkFamily`, `Over.homMkOf`, `Over.homMkLeft`, `Over.homMkOfComp`,
`Over.homMkLift` and `Over.homMkMap` write the morphisms of `Over S₀` with prescribed underlying
morphisms that the comparison uses.
-/

@[expose] public section

noncomputable section

universe t v' v u' u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S₀ : C} {T : Over S₀} {ι : Type t} {U : ι → C}
  (g : ∀ i, U i ⟶ T.left)

/-- The family `Over.homMk (g i) : Over.mk (g i ≫ T.hom) ⟶ T` of `Over S₀` given by a family of
morphisms `g i : U i ⟶ T.left`. -/
abbrev homMkFamily : ∀ i, Over.mk (g i ≫ T.hom) ⟶ T := fun i ↦ Over.homMk (g i)

variable {g}

theorem left_comp_homMkFamily {Y : Over S₀} {q : Y ⟶ T} {i : ι} (f₁ : Y ⟶ Over.mk (g i ≫ T.hom))
    (hf₁ : f₁ ≫ homMkFamily g i = q) : f₁.left ≫ g i = q.left :=
  congrArg CommaMorphism.left hf₁

/-- The morphism `Over.mk (q.left ≫ T.hom) ⟶ Over.mk (g i ≫ T.hom)` with the same underlying
morphism as `f₁ : Y ⟶ Over.mk (g i ≫ T.hom)`. -/
abbrev homMkOfComp {Y : Over S₀} {q : Y ⟶ T} {i : ι} (f₁ : Y ⟶ Over.mk (g i ≫ T.hom))
    (hf₁ : f₁ ≫ homMkFamily g i = q) :
    Over.mk (q.left ≫ T.hom) ⟶ Over.mk (g i ≫ T.hom) :=
  Over.homMk f₁.left (by
    change f₁.left ≫ g i ≫ T.hom = q.left ≫ T.hom
    rw [← Category.assoc, left_comp_homMkFamily f₁ hf₁])

/-- The morphism `Over.mk (q.left ≫ T.hom) ⟶ T` with underlying morphism `q.left`. -/
abbrev homMkLeft {Y : Over S₀} (q : Y ⟶ T) : Over.mk (q.left ≫ T.hom) ⟶ T :=
  Over.homMk q.left rfl

theorem homMkOfComp_comp {Y : Over S₀} {q : Y ⟶ T} {i : ι} (f₁ : Y ⟶ Over.mk (g i ≫ T.hom))
    (hf₁ : f₁ ≫ homMkFamily g i = q) :
    homMkOfComp f₁ hf₁ ≫ homMkFamily g i = homMkLeft q := by
  ext
  exact left_comp_homMkFamily f₁ hf₁

/-- A scheme `W` with `q : W ⟶ T.left`, as the morphism `Over.mk (q ≫ T.hom) ⟶ T`. -/
abbrev homMkOf {W : C} (q : W ⟶ T.left) : Over.mk (q ≫ T.hom) ⟶ T :=
  Over.homMk q rfl

/-- `h : W ⟶ U i` with `h ≫ g i = q`, as a morphism
`Over.mk (q ≫ T.hom) ⟶ Over.mk (g i ≫ T.hom)`. -/
abbrev homMkLift {W : C} (q : W ⟶ T.left) {i : ι} (h : W ⟶ U i) (hh : h ≫ g i = q) :
    Over.mk (q ≫ T.hom) ⟶ Over.mk (g i ≫ T.hom) :=
  Over.homMk h (by
    change h ≫ g i ≫ T.hom = q ≫ T.hom
    rw [← Category.assoc, hh])

theorem homMkLift_comp {W : C} (q : W ⟶ T.left) {i : ι} (h : W ⟶ U i) (hh : h ≫ g i = q) :
    homMkLift q h hh ≫ homMkFamily g i = homMkOf q := by
  ext
  exact hh

/-- `g' : W' ⟶ W` with `g' ≫ q = q'`, as a morphism `Over.mk (q' ≫ T.hom) ⟶ Over.mk (q ≫ T.hom)`. -/
abbrev homMkMap {W W' : C} (q : W ⟶ T.left) (q' : W' ⟶ T.left) (g' : W' ⟶ W) (hq : g' ≫ q = q') :
    Over.mk (q' ≫ T.hom) ⟶ Over.mk (q ≫ T.hom) :=
  Over.homMk g' (by
    change g' ≫ q ≫ T.hom = q' ≫ T.hom
    rw [← Category.assoc, hq])

end CategoryTheory.Over

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat
open Over (homMkFamily left_comp_homMkFamily homMkOfComp homMkLeft homMkOfComp_comp homMkOf
  homMkLift homMkLift_comp homMkMap)

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {S₀ : C}
  {T : Over S₀} {ι : Type t} {U : ι → C} {g : ∀ i, U i ⟶ T.left}

-- As for Mathlib's `pullHom`: the objects of `F.obj _` (a `Cat.of`) must be seen as objects of the
-- underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- A descent datum for `F.restrictAlong (Over.forget S₀)` relative to `homMkFamily g` depends only
on the underlying morphisms: its morphism over `Y` agrees with the one over
`Over.mk (q.left ≫ T.hom)`. -/
theorem DescentData.hom_eq_hom_overMk
    (D : (F.restrictAlong (Over.forget S₀)).DescentData (homMkFamily g)) ⦃Y : Over S₀⦄ (q : Y ⟶ T)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ Over.mk (g i₁ ≫ T.hom)) (f₂ : Y ⟶ Over.mk (g i₂ ≫ T.hom))
    (hf₁ : f₁ ≫ homMkFamily g i₁ = q) (hf₂ : f₂ ≫ homMkFamily g i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ =
      D.hom (Y := Over.mk (q.left ≫ T.hom)) (homMkLeft q) (homMkOfComp f₁ hf₁)
        (homMkOfComp f₂ hf₂) (homMkOfComp_comp f₁ hf₁) (homMkOfComp_comp f₂ hf₂) := by
  let e : Over.mk (q.left ≫ T.hom) ⟶ Y := Over.homMk (𝟙 Y.left) (by
    change 𝟙 Y.left ≫ Y.hom = q.left ≫ T.hom
    rw [Category.id_comp]
    exact (Over.w q).symm)
  have h := D.pullHom_hom e q (homMkLeft q) (by ext; simp [e]) f₁ f₂ hf₁ hf₂
    (homMkOfComp f₁ hf₁) (homMkOfComp f₂ hf₂) (by ext; simp [e]) (by ext; simp [e])
  rw [← h, restrictAlong_pullHom]
  exact (pullHom_id (F := F) _).symm

-- As for Mathlib's `pullHom`: the objects of `F.obj _` (a `Cat.of`) must be seen as objects of the
-- underlying category.
set_option backward.isDefEq.respectTransparency false in
/-- Descent data for `F.restrictAlong (Over.forget S₀)` relative to `homMkFamily g` give descent
data for `F` relative to `g`, with the same objects: a scheme `W` with `q : W ⟶ T.left` is the
object `Over.mk (q ≫ T.hom)` of `Over S₀`. -/
@[simps]
def DescentData.ofOver (D : (F.restrictAlong (Over.forget S₀)).DescentData (homMkFamily g)) :
    F.DescentData g where
  obj := D.obj
  hom W q i₁ i₂ h₁ h₂ hh₁ hh₂ := D.hom (homMkOf q) (homMkLift q h₁ hh₁) (homMkLift q h₂ hh₂)
      (homMkLift_comp q h₁ hh₁) (homMkLift_comp q h₂ hh₂)
  pullHom_hom W' W g' q q' hq i₁ i₂ h₁ h₂ hh₁ hh₂ gh₁ gh₂ hgh₁ hgh₂ := by
    have hgh₁' : gh₁ ≫ g i₁ = q' := by rw [← hgh₁, Category.assoc, hh₁, hq]
    have hgh₂' : gh₂ ≫ g i₂ = q' := by rw [← hgh₂, Category.assoc, hh₂, hq]
    have h := D.pullHom_hom (homMkMap q q' g' hq) (homMkOf q) (homMkOf q') (by ext; exact hq)
      (homMkLift q h₁ hh₁) (homMkLift q h₂ hh₂) (homMkLift_comp q h₁ hh₁) (homMkLift_comp q h₂ hh₂)
      (homMkLift q' gh₁ hgh₁') (homMkLift q' gh₂ hgh₂') (by ext; exact hgh₁) (by ext; exact hgh₂)
    rw [restrictAlong_pullHom] at h
    exact h
  hom_self W q i h hh := D.hom_self _ _ (homMkLift_comp q h hh)
  hom_comp W q i₁ i₂ i₃ h₁ h₂ h₃ hh₁ hh₂ hh₃ := D.hom_comp _ _ _ _ _ _ _

variable (F g) in
-- As for `DescentData.ofOver`.
set_option backward.isDefEq.respectTransparency false in
/-- The functor `DescentData.ofOver`. -/
@[simps]
def DescentData.ofOverFunctor :
    (F.restrictAlong (Over.forget S₀)).DescentData (homMkFamily g) ⥤ F.DescentData g where
  obj D := D.ofOver
  map {D₁ D₂} φ :=
    { hom := φ.hom
      comm W q i₁ i₂ h₁ h₂ hh₁ hh₂ := φ.comm (homMkOf q) (homMkLift q h₁ hh₁) (homMkLift q h₂ hh₂)
        (homMkLift_comp q h₁ hh₁) (homMkLift_comp q h₂ hh₂) }

variable (F g) in
-- As for `DescentData.ofOver`.
set_option backward.isDefEq.respectTransparency false in
/-- `DescentData.ofOverFunctor` is fully faithful: by `DescentData.hom_eq_hom_overMk`, the
compatibility of a family of morphisms over every object of `Over S₀` is its compatibility over
the objects `Over.mk (q ≫ T.hom)`. -/
def DescentData.fullyFaithfulOfOverFunctor : (DescentData.ofOverFunctor F g).FullyFaithful where
  preimage {D₁ D₂} ψ :=
    { hom := ψ.hom
      comm Y q i₁ i₂ y₁ y₂ hy₁ hy₂ := by
        rw [D₁.hom_eq_hom_overMk q y₁ y₂ hy₁ hy₂, D₂.hom_eq_hom_overMk q y₁ y₂ hy₁ hy₂]
        exact ψ.comm q.left y₁.left y₂.left (left_comp_homMkFamily y₁ hy₁)
          (left_comp_homMkFamily y₂ hy₂) }
  map_preimage _ := rfl
  preimage_map _ := rfl

variable (F g) in
-- As for `DescentData.ofOver`; `simp` must use the `simps` lemmas of the constructions.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `toDescentData` of the restriction, followed by `DescentData.ofOverFunctor`, is
`toDescentData` of `F`. -/
def DescentData.toDescentDataOfOverIso :
    (F.restrictAlong (Over.forget S₀)).toDescentData (homMkFamily g) ⋙
      DescentData.ofOverFunctor F g ≅ F.toDescentData g :=
  NatIso.ofComponents (fun M ↦ DescentData.isoMk (fun _ ↦ Iso.refl _) (by
      intro W q i₁ i₂ h₁ h₂ hh₁ hh₂
      dsimp
      rw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id,
        restrictAlong_mapComp'_inv_app (homMkFamily g i₁) (homMkLift q h₁ hh₁) (homMkOf q)
          (homMkLift_comp q h₁ hh₁) M,
        restrictAlong_mapComp'_hom_app (homMkFamily g i₂) (homMkLift q h₂ hh₂) (homMkOf q)
          (homMkLift_comp q h₂ hh₂) M]
      rfl))
    (fun φ ↦ by
      ext i
      dsimp
      simp)

/-- **Descent over `Over S₀`.** If `F` is a stack for the presieve of `g i : U i ⟶ T.left`, then
`F.restrictAlong (Over.forget S₀)` is a stack for the presieve of `Over.homMk (g i)`. -/
theorem isStackFor_restrictAlong_overForget (h : F.IsStackFor (Presieve.ofArrows U g)) :
    (F.restrictAlong (Over.forget S₀)).IsStackFor (Presieve.ofArrows _ (homMkFamily g)) := by
  rw [isStackFor_ofArrows_iff] at h ⊢
  have hF : (F.toDescentData g).IsEquivalence := h
  let Φ := DescentData.ofOverFunctor F g
  have hΦ := DescentData.fullyFaithfulOfOverFunctor F g
  have e := DescentData.toDescentDataOfOverIso F g
  have : Φ.Full := hΦ.full
  have : Φ.Faithful := hΦ.faithful
  have : Φ.EssSurj := ⟨fun E ↦ ⟨((F.restrictAlong (Over.forget S₀)).toDescentData
      (homMkFamily g)).obj ((F.toDescentData g).objPreimage E),
    ⟨e.app _ ≪≫ (F.toDescentData g).objObjPreimageIso E⟩⟩⟩
  have : Φ.IsEquivalence := { }
  have : ((F.restrictAlong (Over.forget S₀)).toDescentData (homMkFamily g) ⋙ Φ).IsEquivalence :=
    @Functor.isEquivalence_of_iso _ _ _ _ _ _ e.symm hF
  exact Functor.isEquivalence_of_comp_right _ Φ

end CategoryTheory.Pseudofunctor
