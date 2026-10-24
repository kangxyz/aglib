/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange

/-! Focused consumer of the base change of the family Picard presheaf along `g : S' ⟶ S`
(Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65, at the presheaf level), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry Scheme.RelativePicard Scheme.Modules.Invertible

universe u

variable {S S' X : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)

/-- The family of `X ×_S S' ⟶ S'` is the family of `p` along `Over.map g`, with the canonical
comparison of literal fibre products as components. -/
example (T : Over S') :
    (familySchemeBaseChangeIso p g).app T = pullbackLeftPullbackSndIso p g T.hom :=
  familySchemeBaseChangeIso_app p g T

/-- `Pic((X ×_S S') ×_{S'} T) ≅ Pic(X ×_S T)` naturally in `T`, by pullback along the inverse
comparison. -/
example (T : (Over S')ᵒᵖ) (a : PicardGroup (pullback (pullback.snd p g) T.unop.hom)) :
    ((familyPicardFunctorBaseChangeIso p g).hom.app T).hom a =
      pullbackClass (pullbackLeftPullbackSndIso p g T.unop.hom).inv a :=
  familyPicardFunctorBaseChangeIso_hom_app_apply p g T a

/-- Naturality, in the form of the naturality square of the isomorphism. -/
example {T T' : (Over S')ᵒᵖ} (f : T ⟶ T') :
    (familyPicardFunctor (pullback.snd p g)).map f ≫
        (familyPicardFunctorBaseChangeIso p g).hom.app T' =
      (familyPicardFunctorBaseChangeIso p g).hom.app T ≫
        (familyPicardFunctor p).map ((Over.map g).op.map f) :=
  (familyPicardFunctorBaseChangeIso p g).hom.naturality f

/-- Compatibility with the base pullbacks. -/
example :
    basePullback (pullback.snd p g) ≫ (familyPicardFunctorBaseChangeIso p g).hom =
      Functor.whiskerLeft (Over.map g).op (basePullback p) :=
  basePullback_comp_familyPicardFunctorBaseChangeIso_hom p g

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familyPicardFunctorBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyPicardFunctorBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.basePullback_comp_familyPicardFunctorBaseChangeIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms basePullback_comp_familyPicardFunctorBaseChangeIso_hom
