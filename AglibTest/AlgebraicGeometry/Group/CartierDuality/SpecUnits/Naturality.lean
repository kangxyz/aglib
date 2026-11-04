/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits.Naturality

/-! Native unit coordinates remain natural across arbitrary commutative coefficient bases. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {K L : Type u} [CommRing K] [CommRing L]

example (A : CommAlgCat.{u} K) (B : CommAlgCat.{u} L) (f : A →+* B) (u : Aˣ) :
    Spec.map (CommRingCat.ofHom f) ≫ (specUnitMap A u).left ≫
        CategoryTheory.Limits.prod.snd =
      (specUnitMap B (Units.map f.toMonoidHom u)).left ≫
        CategoryTheory.Limits.prod.snd :=
  specUnitMap_laurent_naturality A B f u
