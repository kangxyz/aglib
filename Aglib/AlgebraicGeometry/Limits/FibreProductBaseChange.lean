/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of the second factor of a fibre product

Let `p : X ⟶ S` be a morphism of schemes and `f : T' ⟶ T` a morphism over `S`, with structure
maps `g : T ⟶ S` and `g' : T' ⟶ S` (`f ≫ g = g'`). The map
`pullback.map p g' p g (𝟙 X) f (𝟙 S) : X ×_S T' ⟶ X ×_S T` (the map of
`RelativePicard.familyScheme p` at `f`) and the second projections form a cartesian square over
`f` (`Scheme.isPullback_pullbackMap_snd`): `X ×_S T'` is the base change of `X ×_S T ⟶ T` along
`f`. The proof pastes the two pullback squares over `S`; no hypothesis on `p`, `g`, `g'` or `f`
is used.

Consumers: the Hilbert functor of an immersed scheme (`HilbertScheme/Immersed/Functor`, base change
of proper closed subschemes of `Y ×_S T`) and the base change of relative effective Cartier
divisors on `X ×_S T` along `T' ⟶ T`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- **Base change of the second factor of a fibre product**: for `p : X ⟶ S` and `f : T' ⟶ T`
with `f ≫ g = g'`, the square formed by `pullback.map p g' p g (𝟙 X) f (𝟙 S)`, the second
projections `X ×_S T' ⟶ T'` and `X ×_S T ⟶ T`, and `f` is cartesian. -/
theorem isPullback_pullbackMap_snd {X S T T' : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
    (g' : T' ⟶ S) (f : T' ⟶ T) (h : f ≫ g = g') :
    IsPullback (pullback.map p g' p g (𝟙 X) f (𝟙 S) (by simp) (by rw [Category.comp_id, h]))
      (pullback.snd p g') (pullback.snd p g) f := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p g)
  rw [pullback.lift_fst, Category.comp_id, h]
  exact IsPullback.of_hasPullback p g'

end AlgebraicGeometry.Scheme
