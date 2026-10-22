/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Limits checked on an open cover of the base

A cone of schemes over a fixed base is limiting if its pullback to every
member of a supplied open cover is limiting. The universal morphism is
constructed by gluing, so no existence of the original limit is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u v w

namespace AlgebraicGeometry.Scheme.Cover

variable {I : Type v} [Category.{w} I] {S : Scheme.{u}}
  (𝒰 : S.OpenCover) (D : I ⥤ Over S) (c : Cone D)
  (hc : ∀ a, IsLimit ((Over.pullback (𝒰.f a)).mapCone c))

include hc in
/-- Local limit uniqueness implies uniqueness for maps into the original cone. -/
lemma cone_hom_ext_of_pullback {T : Over S} (f g : T ⟶ c.pt)
    (hfg : ∀ i, f ≫ c.π.app i = g ≫ c.π.app i) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ T.hom)
  intro a
  have h : (Over.pullback (𝒰.f a)).map f = (Over.pullback (𝒰.f a)).map g := by
    apply (hc a).hom_ext
    intro i
    simpa only [Functor.mapCone_π_app, ← Functor.map_comp] using
      congrArg (Over.pullback (𝒰.f a)).map (hfg i)
  have h' := congrArg (fun k => k.left ≫ pullback.fst c.pt.hom (𝒰.f a)) h
  simpa using h'

namespace LimitGluing

variable (s : Cone D)

/-- The universal map on one pullback chart of an arbitrary test cone. -/
def localMap (a : 𝒰.I₀) : (𝒰.pullback₁ s.pt.hom).X a ⟶ c.pt.left :=
  ((hc a).lift ((Over.pullback (𝒰.f a)).mapCone s)).left ≫
    pullback.fst c.pt.hom (𝒰.f a)

@[reassoc (attr := simp)]
lemma localMap_base (a : 𝒰.I₀) :
    localMap 𝒰 D c hc s a ≫ c.pt.hom = (𝒰.pullback₁ s.pt.hom).f a ≫ s.pt.hom := by
  have hw := Over.w ((hc a).lift ((Over.pullback (𝒰.f a)).mapCone s))
  change _ ≫ pullback.snd c.pt.hom (𝒰.f a) = pullback.snd s.pt.hom (𝒰.f a) at hw
  change localMap 𝒰 D c hc s a ≫ c.pt.hom = pullback.fst s.pt.hom (𝒰.f a) ≫ s.pt.hom
  rw [localMap, Category.assoc, pullback.condition, ← Category.assoc, hw]
  exact pullback.condition.symm

@[reassoc (attr := simp)]
lemma localMap_fac (a : 𝒰.I₀) (i : I) :
    localMap 𝒰 D c hc s a ≫ (c.π.app i).left =
      (𝒰.pullback₁ s.pt.hom).f a ≫ (s.π.app i).left := by
  have h := congrArg (fun k => k.left ≫ pullback.fst (D.obj i).hom (𝒰.f a))
    ((hc a).fac ((Over.pullback (𝒰.f a)).mapCone s) i)
  simpa [localMap, Category.assoc] using h

/-- The local universal maps agree on the literal intersections of the source cover. -/
lemma compatible (a b : 𝒰.I₀) :
    pullback.fst ((𝒰.pullback₁ s.pt.hom).f a) ((𝒰.pullback₁ s.pt.hom).f b) ≫
      localMap 𝒰 D c hc s a =
    pullback.snd _ _ ≫ localMap 𝒰 D c hc s b := by
  let T : Over S := Over.mk
    (pullback.fst ((𝒰.pullback₁ s.pt.hom).f a) ((𝒰.pullback₁ s.pt.hom).f b) ≫
      (𝒰.pullback₁ s.pt.hom).f a ≫ s.pt.hom)
  let f : T ⟶ c.pt := Over.homMk (pullback.fst _ _ ≫ localMap 𝒰 D c hc s a)
    (by simp [T])
  let g : T ⟶ c.pt := Over.homMk (pullback.snd _ _ ≫ localMap 𝒰 D c hc s b)
    (by simp only [Category.assoc, localMap_base, T, Over.mk_left, Over.mk_hom]
        exact (pullback.condition_assoc (f := (𝒰.pullback₁ s.pt.hom).f a)
          (g := (𝒰.pullback₁ s.pt.hom).f b) s.pt.hom).symm)
  have h : f = g := cone_hom_ext_of_pullback 𝒰 D c hc f g (fun i => by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, f, g, Over.homMk_left, Category.assoc, localMap_fac]
    exact pullback.condition_assoc (f := (𝒰.pullback₁ s.pt.hom).f a)
      (g := (𝒰.pullback₁ s.pt.hom).f b) (s.π.app i).left)
  exact congrArg (fun k => k.left) h

/-- The global universal morphism obtained from the chartwise universal morphisms. -/
def lift : s.pt ⟶ c.pt :=
  Over.homMk (Scheme.Cover.glueMorphisms (𝒰.pullback₁ s.pt.hom)
    (localMap 𝒰 D c hc s) (compatible 𝒰 D c hc s)) (by
      apply Scheme.Cover.hom_ext (𝒰.pullback₁ s.pt.hom)
      intro a
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
      exact localMap_base 𝒰 D c hc s a)

@[reassoc (attr := simp)]
lemma lift_fac (i : I) : lift 𝒰 D c hc s ≫ c.π.app i = s.π.app i := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ s.pt.hom)
  intro a
  change (𝒰.pullback₁ s.pt.hom).f a ≫
    (Scheme.Cover.glueMorphisms (𝒰.pullback₁ s.pt.hom)
      (localMap 𝒰 D c hc s) (compatible 𝒰 D c hc s)) ≫ (c.π.app i).left = _
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact localMap_fac 𝒰 D c hc s a i

end LimitGluing

/-- Limits of schemes over a fixed base can be checked on an arbitrary open cover.
The cone point, all projections and the structural map are retained literally. -/
def isLimit_of_pullback : IsLimit c where
  lift s := LimitGluing.lift 𝒰 D c hc s
  fac s i := LimitGluing.lift_fac 𝒰 D c hc s i
  uniq s m hm := cone_hom_ext_of_pullback 𝒰 D c hc m _ (fun i => by
    rw [hm i, LimitGluing.lift_fac])

end AlgebraicGeometry.Scheme.Cover
