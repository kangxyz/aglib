/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate

/-! The dual construction consumes the original finite commutative native group object. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

example : (coordinateHopf G : Type u) = Γ(G.X.left, ⊤) := coordinateHopf_carrier G
example : FiniteDimensional k (coordinateHopf G) := inferInstance
example : Coalgebra.IsCocomm k (coordinateHopf G) := inferInstance
example : IsFinite (dualGroup G).X.hom := inferInstance
example : Flat (dualGroup G).X.hom := inferInstance
example : IsCommMonObj (dualGroup G).X := inferInstance

example : (coordinateSpecIso G).inv.hom.hom.left = G.X.left.toSpecΓ :=
  coordinateSpecIso_inv_left G

/-- The standard Scheme-over instance is the native pullback implementation used by kernels. -/
example {k : Type u} [Field k] :
    (inferInstance : CartesianMonoidalCategory (FScheme k)) =
      Over.cartesianMonoidalCategory (AlgebraicGeometry.Scheme.OverField.Base k) := rfl
