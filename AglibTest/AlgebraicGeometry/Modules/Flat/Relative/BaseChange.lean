/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.BaseChange

/-! Focused consumers of the base change of relative flatness (Stacks Project, Tag 01U8), with
axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Base change of relative flatness along an arbitrary pullback square. -/
example {X X' S S' : Scheme.{u}} {g : X' ⟶ X} {q : X' ⟶ S'} {p : X ⟶ S} {f : S' ⟶ S}
    (h : IsPullback g q p f) (M : X.Modules) [M.IsQuasicoherent]
    (hM : Scheme.Modules.relativeFlat p M) :
    Scheme.Modules.relativeFlat q ((Scheme.Modules.pullback g).obj M) :=
  Scheme.Modules.relativeFlat_pullback_of_isPullback h M hM

/-- The affine form: base change of a family over `Spec A` along `Spec A' ⟶ Spec A`. -/
example {X : Scheme.{u}} {A A' : CommRingCat.{u}} (p : X ⟶ Spec A) (σ : A ⟶ A')
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.relativeFlat p M) :
    Scheme.Modules.relativeFlat (pullback.snd p (Spec.map σ))
      ((Scheme.Modules.pullback (pullback.fst p (Spec.map σ))).obj M) :=
  Scheme.Modules.relativeFlat_pullback_snd p (Spec.map σ) M hM

/-- Relative flatness between affine schemes is flatness of the affine sections. -/
example {U Y : Scheme.{u}} [IsAffine U] [IsAffine Y] (π : U ⟶ Y) (N : U.Modules)
    [N.IsQuasicoherent] :
    Scheme.Modules.relativeFlat π N ↔ Module.Flat Γ(Y, ⊤)
      ((ModuleCat.restrictScalars π.appTop.hom).obj
        ((Scheme.Modules.affineΓFunctor U).obj N)) :=
  Scheme.Modules.relativeFlat_iff_flat_affineΓFunctor π N

/-- Composition with an open immersion of the target in both directions. -/
example {W V Y : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) [IsOpenImmersion j] (N : W.Modules) :
    Scheme.Modules.relativeFlat (b ≫ j) N ↔ Scheme.Modules.relativeFlat b N :=
  ⟨Scheme.Modules.relativeFlat_of_comp_isOpenImmersion b j,
    Scheme.Modules.relativeFlat_comp_of_isOpenImmersion b j⟩

/-- The algebraic core: flatness of a scalar extension along a pushout of rings. -/
example {A A' B C : CommRingCat.{u}} (φ : A ⟶ B) (σ : A ⟶ A') (α : B ⟶ C) (β : A' ⟶ C)
    (h : IsPushout σ φ β α) (E : ModuleCat.{u} B)
    (hE : Module.Flat A ((ModuleCat.restrictScalars φ.hom).obj E)) :
    Module.Flat A' ((ModuleCat.restrictScalars β.hom).obj
      ((ModuleCat.extendScalars α.hom).obj E)) :=
  ModuleCat.flat_extendScalars_of_isPushout φ σ α β h E hE

/--
info: 'ModuleCat.flat_extendScalars_of_isPushout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.flat_extendScalars_of_isPushout

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_comp_of_isOpenImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_comp_of_isOpenImmersion

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_affineΓFunctor_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.flat_affineΓFunctor_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_of_flat_affineΓFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_of_flat_affineΓFunctor

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_flat_affineΓFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_flat_affineΓFunctor

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd
