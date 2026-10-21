/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Group.MultiplicationEtale
import Aglib.AlgebraicGeometry.Group.MultiplicationKernel

/-!
# Native multiplication-kernel consumer of a nontrivial point witness

The arbitrary-characteristic client supplies finiteness of the existing actual
kernel carrier. The characteristic-zero client supplies etaleness of its actual
structural morphism. Neither client introduces a point-coordinate replacement
or assumes a degree formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Group.Multiplication
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Grp (FScheme k)) [IsCommMonObj G.X]
    (hG : Curve.Properties G.X) (n : ℕ) {T : FScheme k}
    (x : T ⟶ G.X) (hx : x ^ n ≠ 1) : Finite (finiteTorsionPoints G n) := by
  obtain ⟨hf, _⟩ := multiplication_finite_surjective_of_ne_one G hG n
    (multiplication_ne_one_of_point G n x hx)
  let : IsFinite (multiplication G n).left := hf
  infer_instance

example {k : Type u} [Field k] [CharZero k] (G : Grp (FScheme k)) [IsCommMonObj G.X]
    (hG : Curve.Properties G.X) (n : ℕ) {T : FScheme k}
    (x : T ⟶ G.X) (hx : x ^ n ≠ 1) : Etale (kernelScheme G n).hom := by
  obtain ⟨_, he, _⟩ := multiplication_finite_etale_of_point G hG n x hx
  let : Etale (multiplication G n).left := he
  change Etale (pullback.snd (multiplication G n).left η[G.X].left)
  infer_instance
