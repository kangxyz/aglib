/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Functor

/-! Actual coordinate pullback and contravariant dual maps on the original finite groups. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {k : Type u} [Field k] {G H K : Grp (FScheme k)}
  [IsFinite G.X.hom] [IsFinite H.X.hom] [IsFinite K.X.hom]

example (f : G ⟶ H) :
    CommRingCat.ofHom (coordinateMap f).hom.toAlgHom.toRingHom = f.hom.hom.left.appTop :=
  coordinateMap_appTop f

example {f g : G ⟶ H} (h : coordinateMap f = coordinateMap g) : f = g :=
  coordinateMap_injective h

variable [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj K.X]

example : dualMap (𝟙 G) = 𝟙 (dualGroup G) := dualMap_id

example (f : G ⟶ H) (g : H ⟶ K) : dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  dualMap_comp f g
