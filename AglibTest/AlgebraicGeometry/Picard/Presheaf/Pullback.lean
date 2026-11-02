/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf.Pullback

/-! # Source pullback and base change on all tests, with no flatness or origin assumption -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme.RelativePicard
open Scheme.Modules.Invertible

universe u

example {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S)
    (a : PicardGroup (pullback Y.hom T.hom)) :
    ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T)).hom
        (pullbackClass (familyMapOfHom f T) a) =
      ((fppfPicardPullback f).hom.app (op T)).hom
        (((quotientProjection Y.hom ≫ toFppfPicardSheaf Y.hom).app (op T)).hom a) :=
  fppfPicardPullback_class f T a

example {S S' : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (b : S' ⟶ S) :
    (fppfPicardPullback ((Over.pullback b).map f)).hom ≫
        (fppfPicardSheafBaseChangeIso X.hom b).hom =
      (fppfPicardSheafBaseChangeIso Y.hom b).hom ≫
        Functor.whiskerLeft (Over.map b).op (fppfPicardPullback f).hom :=
  fppfPicardPullback_baseChange f b

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfPicardPullback_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.fppfPicardPullback_baseChange
