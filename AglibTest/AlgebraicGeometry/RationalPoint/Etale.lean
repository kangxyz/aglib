/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Etale

/-! # Surjective cotangent pullback on the original smooth pointed endomorphism -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] {X : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (f : X ⟶ X) (h : x ≫ f = x)
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hc : Function.Surjective (Cotangent.map x x f h)) :
    ∃ U : X.left.Opens, (Cotangent.pointData x).point ∈ U ∧ Etale (U.ι ≫ f.left) :=
  Cotangent.exists_etale_neighborhood_of_surjective x f h d hc
