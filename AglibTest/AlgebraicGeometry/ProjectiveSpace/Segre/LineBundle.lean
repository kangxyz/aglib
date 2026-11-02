/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.LineBundle

/-! The original Segre O(1) comparison is independent of field and finiteness assumptions. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example (R : Type u) [CommRing R] (ι κ : Type u) :
    (Scheme.Modules.pullback (Segre.embedding R ι κ)).obj (twistingSheaf R (ι × κ) 1) ≅
      tensorSheaf (Segre.product R ι κ)
        ((Scheme.Modules.pullback (Segre.first R ι κ)).obj (twistingSheaf R ι 1))
        ((Scheme.Modules.pullback (Segre.second R ι κ)).obj (twistingSheaf R κ 1)) :=
  Segre.embeddingTwistingPullbackIso

example {R : Type u} [CommRing R] {ι κ : Type u} {Y : Scheme.{u}}
    (f : Y ⟶ ProjectiveSpace R ι) (g : Y ⟶ ProjectiveSpace R κ) :
    pullbackClass (Segre.map f g) (classOf _ (twistingLineBundle R (ι × κ) 1)) =
      pullbackClass f (classOf _ (twistingLineBundle R ι 1)) +
        pullbackClass g (classOf _ (twistingLineBundle R κ 1)) :=
  Segre.pullbackClass_twisting_one f g

end
