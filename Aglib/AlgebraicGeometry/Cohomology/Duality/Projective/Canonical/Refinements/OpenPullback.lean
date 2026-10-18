/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback

/-!
# The original pullback comparison in an open square

The original restriction-to-pullback isomorphisms and pullback composition
isomorphisms compare restriction of a pullback with pullback of a restriction.
The vertical arrows are arbitrary; only the two horizontal arrows are open.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual mixed open/pullback square, retaining all original comparison maps. -/
def canonicalPullbackOpenSquareIso {X Y X' Y' : Scheme.{u}}
    (i : X ⟶ Y) (i' : X' ⟶ Y') (jX : X' ⟶ X) (jY : Y' ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY] (h : jX ≫ i = i' ≫ jY) :
    pullback i ⋙ restrictFunctor jX ≅ restrictFunctor jY ⋙ pullback i' :=
  pullbackOpenSquare jX i' i jY h

end AlgebraicGeometry.Scheme.Modules
