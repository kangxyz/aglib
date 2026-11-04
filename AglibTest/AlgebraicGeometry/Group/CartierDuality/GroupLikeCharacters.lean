/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.GroupLikeCharacters

/-! Characters use the native Hopf Spec and the existing multiplicative group over any ring. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Group
open CartierDuality

universe u

variable {R : Type u} [CommRing R] (A : CommHopfAlgCat.{u} R)

example : GroupLike R A ≃
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op A) ⟶
      MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) := groupLikeCharacterEquiv A

example (a : GroupLike R A) :
    specUnitsEquiv (CommAlgCat.of R A) (groupLikeCharacterEquiv A a).hom.hom =
      GroupLike.toUnits R a := groupLikeCharacterEquiv_units A a

example {B : CommHopfAlgCat.{u} R} (f : A ⟶ B) (a : GroupLike R A) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op ≫ groupLikeCharacter A a =
      groupLikeCharacter B ⟨f.hom a.val, a.2.map f.hom⟩ :=
  groupLikeCharacter_naturality f a
