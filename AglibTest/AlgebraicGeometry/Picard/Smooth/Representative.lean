/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.Representative

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard

universe u

example {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion i]
    [Flat (i ≫ toSpec k ι)] [GeometricallyIntegral (i ≫ toSpec k ι)]
    {N : ℕ} (e : ι ≃ Fin (N + 1)) [IsIntegral X]
    (hd : topologicalKrullDim X = 1)
    (P : LocallyNoetherianOver (Spec (.of k)))
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) : Smooth P.obj.hom :=
  smooth_representative_of_curve i e hd P R
