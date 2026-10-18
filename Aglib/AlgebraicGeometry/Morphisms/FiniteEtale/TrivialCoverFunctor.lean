/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverSheafQuotient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverBaseChange

/-! The actual finite coproduct cover, functorially in its labels, and its
geometric fibre. These maps allow a finite action to be made constant locally. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u

/-- The morphism of finite trivial covers that sends the summand labelled `a`
to the summand labelled `f a`. -/
def trivialCoverMap (X : Scheme.{u}) {A B : Type u} [Finite A] [Finite B] (f : A → B) :
    trivialCover X A ⟶ trivialCover X B :=
  Sigma.desc (fun a => trivialCoverι X B (f a))

@[reassoc] theorem trivialCoverι_map (X : Scheme.{u}) {A B : Type u}
    [Finite A] [Finite B] (f : A → B) (a : A) :
    trivialCoverι X A a ≫ trivialCoverMap X f = trivialCoverι X B (f a) :=
  Sigma.ι_comp_desc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The functor taking a finite type to its trivial finite étale cover over `X`,
and a function of labels to `trivialCoverMap X`. -/
def trivialCoverFunctor (X : Scheme.{u}) : FintypeCat.{u} ⥤ Scheme.FiniteEtale X where
  obj A := trivialCover X A
  map f := trivialCoverMap X f
  map_id A := by
    apply Sigma.hom_ext
    intro a
    exact (trivialCoverι_map X (𝟙 A) a).trans (Category.comp_id _).symm
  map_comp f g := by
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, trivialCoverι_map, trivialCoverι_map, trivialCoverι_map]
    rfl

theorem trivialCoverFiberPoint_map {X : Scheme.{u}} {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) {A B : Type u} [Finite A] [Finite B]
    (f : A → B) (a : A) :
    (fiberToFinite s).map (trivialCoverMap X f) (trivialCoverFiberPoint A s a) =
      trivialCoverFiberPoint B s (f a) := by
  apply Over.OverMorphism.ext
  change (s ≫ (trivialCoverι X A a).hom.left) ≫ (trivialCoverMap X f).hom.left = _
  rw [Category.assoc]
  exact congrArg (fun k : terminalCover X ⟶ trivialCover X B => s ≫ k.hom.left)
    (trivialCoverι_map X f a)

/-- The comparison uses actual points and postcomposition, including empty labels. -/
def trivialCoverFunctorFiberIso {X : Scheme.{u}} {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    𝟭 FintypeCat.{u} ≅ trivialCoverFunctor X ⋙ fiberToFinite s :=
  NatIso.ofComponents (fun A =>
    { hom := FintypeCat.homMk (trivialCoverFiberEquiv A s)
      inv := FintypeCat.homMk (trivialCoverFiberEquiv A s).symm
      hom_inv_id := by ext a; exact (trivialCoverFiberEquiv A s).symm_apply_apply a
      inv_hom_id := by ext a; exact (trivialCoverFiberEquiv A s).apply_symm_apply a })
    (fun f => by ext a; exact (trivialCoverFiberPoint_map s f a).symm)

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d0e11d509fb3ca1381c00c2db278022f89f8f036d3d8bf5d54d18f0efbec0429.
Definitions, hypotheses and universes are retained modulo native names. -/
