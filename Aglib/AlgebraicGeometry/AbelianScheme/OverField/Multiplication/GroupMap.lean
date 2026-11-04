/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Finite

/-! Positive multiplication properties on the original bundled group map. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

/-- The original bundled multiplication map is the same finite flat
surjective map at every positive level. -/
theorem multiplicationHom_finite_flat_surjective {k : Type u} [Field k]
    (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] (n : ℕ) (hn : 0 < n) :
    let f := MultiplicationKernel.multiplicationHom G n
    IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  simpa only [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
    using multiplication_finite_flat_surjective_of_isHProjective G n hn

end AlgebraicGeometry.Scheme.Group.Multiplication
