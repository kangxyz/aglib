/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Group.MultiplicationCotangent
import Aglib.AlgebraicGeometry.Group.MultiplicationKernel

/-!
# Actual multiplication-kernel consumers of the first-order theorem

These examples are source-only. Client checks are disabled by the current
validation policy; this module has not been compiled.

The existing literal kernel now obtains finiteness from an invertible natural
scalar, and etaleness in characteristic zero. The clients supply no nonconstant
point, dominance, finite-map or etaleness assumption.
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
    (hG : Curve.Properties G.X) (n : ℕ) (hn : IsUnit (n : k)) :
    Finite (finiteTorsionPoints G n) := by
  let : IsFinite (multiplication G n).left :=
    (multiplication_finite_surjective_of_isUnit G hG n hn).1
  infer_instance

example {k : Type u} [Field k] [CharZero k] (G : Grp (FScheme k)) [IsCommMonObj G.X]
    (hG : Curve.Properties G.X) (n : ℕ) (hn : 0 < n) :
    IsFinite (kernelScheme G n).hom ∧ Etale (kernelScheme G n).hom := by
  obtain ⟨hf, he, _⟩ := multiplication_finite_etale_of_pos G hG n hn
  let : IsFinite (multiplication G n).left := hf
  let : Etale (multiplication G n).left := he
  constructor
  · infer_instance
  · change Etale (pullback.snd (multiplication G n).left η[G.X].left)
    infer_instance
