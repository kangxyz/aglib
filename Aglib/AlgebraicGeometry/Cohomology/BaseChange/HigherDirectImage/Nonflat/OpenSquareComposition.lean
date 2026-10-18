/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Descent.Modules.RestrictPullback
public import Aglib.CategoryTheory.Adjunction.Mates

/-!
# Composition of the original pullback and open-restriction squares

The native comparison for two successive commuting squares agrees with the
comparison for the pasted square. The proof uses conjugate transformations
of the original adjunctions, whose pushforward comparisons are literal maps
on the original sections. No cartesian or flatness hypothesis is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem conjugate_restrictPullback_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (pullbackPushforwardAdjunction f) (restrictAdjunction f)
      (restrictFunctorIsoPullback f).hom = 𝟙 (pushforward f) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

private theorem conjugate_restrictPullback_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (restrictAdjunction f) (pullbackPushforwardAdjunction f)
      (restrictFunctorIsoPullback f).inv = 𝟙 (pushforward f) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

private theorem conjugate_pullbackComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  apply (cancel_mono (pushforwardComp f g).hom).mp
  rw [← conjugateEquiv_pullbackComp_inv, conjugateEquiv_comp, Iso.inv_hom_id,
    conjugateEquiv_id, conjugateEquiv_pullbackComp_inv, Iso.inv_hom_id]

private theorem conjugate_pullbackCongr_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
  subst g
  ext M U : 3
  simp [pullbackCongr]

private theorem conjugate_restrictComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  have h : (restrictFunctorIsoPullback (f ≫ g)).hom ≫ (pullbackComp f g).inv =
      (restrictFunctorComp f g).hom ≫
        whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
        whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom := by
    apply NatTrans.ext
    funext M
    exact restrictFunctorIsoPullback_comp_hom_app f g M
  have hc := congrArg (conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (restrictAdjunction (f ≫ g))) h
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (f ≫ g)),
    ← conjugateEquiv_comp _ ((restrictAdjunction g).comp (restrictAdjunction f)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f))] at hc
  rw [conjugateEquiv_pullbackComp_inv, conjugate_restrictPullback_hom,
    conjugateEquiv_whiskerLeft, conjugate_restrictPullback_hom,
    conjugateEquiv_whiskerRight, conjugate_restrictPullback_hom] at hc
  simpa only [whiskerLeft_id', whiskerRight_id', Category.id_comp, Category.comp_id]
    using hc.symm

private theorem conjugate_restrictComp_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv (restrictAdjunction (f ≫ g))
      ((restrictAdjunction g).comp (restrictAdjunction f)) (restrictFunctorComp f g).inv =
      (pushforwardComp f g).inv := by
  apply (cancel_mono (pushforwardComp f g).hom).mp
  rw [← conjugate_restrictComp_hom, conjugateEquiv_comp, Iso.hom_inv_id,
    conjugateEquiv_id, conjugate_restrictComp_hom, Iso.inv_hom_id]

/-- The original pullback and open-restriction comparison is conjugate to
the native composition and equality maps of the original pushforward functors. -/
theorem pullbackOpenSquare_conjugate_hom
    {W X V Y : Scheme.{u}} (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a] (h : p ≫ f = q ≫ a) :
    conjugateEquiv ((restrictAdjunction a).comp (pullbackPushforwardAdjunction q))
      ((pullbackPushforwardAdjunction f).comp (restrictAdjunction p))
      (pullbackOpenSquare p q f a h).hom =
      (pushforwardComp q a).hom ≫ (pushforwardCongr h).inv ≫
        (pushforwardComp p f).inv := by
  simp only [pullbackOpenSquare, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction p)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (p ≫ f)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (q ≫ a)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction a).comp (pullbackPushforwardAdjunction q))]
  rw [conjugateEquiv_whiskerRight, conjugate_restrictPullback_inv,
    conjugateEquiv_pullbackComp_inv, conjugate_pullbackCongr_hom,
    conjugate_pullbackComp_hom, conjugateEquiv_whiskerLeft,
    conjugate_restrictPullback_hom]
  simp only [whiskerLeft_id', whiskerRight_id', Category.id_comp, Category.comp_id,
    Category.assoc]

private theorem pullbackOpenSquare_comp_hom
    {W X V Y W' V' : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a]
    (c : W' ⟶ W) (d : V' ⟶ V) (r : W' ⟶ V')
    [IsOpenImmersion c] [IsOpenImmersion d]
    (wp : p ≫ f = q ≫ a) (wc : c ≫ q = r ≫ d)
    (wt : (c ≫ p) ≫ f = r ≫ (d ≫ a)) :
    (pullbackOpenSquare (c ≫ p) r f (d ≫ a) wt).hom =
      whiskerLeft (pullback f) (restrictFunctorComp c p).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight (pullbackOpenSquare p q f a wp).hom (restrictFunctor c) ≫
        (associator _ _ _).hom ≫
        whiskerLeft (restrictFunctor a) (pullbackOpenSquare c r q d wc).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight (restrictFunctorComp d a).inv (pullback r) := by
  apply (conjugateEquiv
    ((restrictAdjunction (d ≫ a)).comp (pullbackPushforwardAdjunction r))
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction (c ≫ p)))).injective
  rw [pullbackOpenSquare_conjugate_hom]
  rw [← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction f).comp
        ((restrictAdjunction p).comp (restrictAdjunction c))),
    ← conjugateEquiv_comp _
      (((pullbackPushforwardAdjunction f).comp (restrictAdjunction p)).comp
        (restrictAdjunction c)),
    ← conjugateEquiv_comp _
      (((restrictAdjunction a).comp (pullbackPushforwardAdjunction q)).comp
        (restrictAdjunction c)),
    ← conjugateEquiv_comp _
      ((restrictAdjunction a).comp
        ((pullbackPushforwardAdjunction q).comp (restrictAdjunction c))),
    ← conjugateEquiv_comp _
      ((restrictAdjunction a).comp
        ((restrictAdjunction d).comp (pullbackPushforwardAdjunction r))),
    ← conjugateEquiv_comp _
      (((restrictAdjunction a).comp (restrictAdjunction d)).comp
        (pullbackPushforwardAdjunction r))]
  rw [conjugateEquiv_whiskerRight, conjugate_restrictComp_inv,
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    pullbackOpenSquare_conjugate_hom, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, pullbackOpenSquare_conjugate_hom,
    conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    conjugate_restrictComp_hom]
  ext M U : 3
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Hom.comp_app, pushforward_map_app,
    Functor.map_comp, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, Category.id_comp, Category.comp_id]
  change M.presheaf.map _ =
    ((𝟙 _ ≫ 𝟙 _ ≫ M.presheaf.map _ ≫ 𝟙 _) ≫ 𝟙 _ ≫ M.presheaf.map _) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rw [← M.presheaf.map_comp]
  congr 1

/-- Successive commuting squares of open restrictions retain the original
pullback-square comparison and the original restriction-composition maps. -/
theorem pullbackOpenSquare_comp_hom_app
    {W X V Y W' V' : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a]
    (c : W' ⟶ W) (d : V' ⟶ V) (r : W' ⟶ V')
    [IsOpenImmersion c] [IsOpenImmersion d]
    (wp : p ≫ f = q ≫ a) (wc : c ≫ q = r ≫ d)
    (wt : (c ≫ p) ≫ f = r ≫ (d ≫ a)) (E : Y.Modules) :
    (pullbackOpenSquare (c ≫ p) r f (d ≫ a) wt).hom.app E =
      (restrictFunctorComp c p).hom.app ((pullback f).obj E) ≫
        (restrictFunctor c).map ((pullbackOpenSquare p q f a wp).hom.app E) ≫
        (pullbackOpenSquare c r q d wc).hom.app (E.restrict a) ≫
        (pullback r).map ((restrictFunctorComp d a).inv.app E) := by
  have h := congr_app (pullbackOpenSquare_comp_hom p q f a c d r wp wc wt) E
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id] using h

end AlgebraicGeometry.Scheme.Modules
