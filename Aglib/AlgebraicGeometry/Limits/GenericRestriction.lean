/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericFiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Actual generic restriction of a scheme map over a DVR

Source: R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing declarations, chosen maps and explicit evidence boundaries are preserved.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.GenericRestriction` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`671b113e307d353c1e40f2a8f60f6fc03093c0d1acb31b385eb6b8fbef0e3455`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Pullback.GenericRestriction

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual generic restriction of an over-DVR morphism. -/
def genericRestriction {X Z : Scheme.{u}} (πX : X ⟶ Spec (.of R))
    (πZ : Z ⟶ Spec (.of R)) (f : X ⟶ Z) (hf : f ≫ πZ = πX) :
    pullback πX (_root_.AlgebraicGeometry.Scheme.LocalRing.GenericFiber.baseMap R F) ⟶ pullback
        πZ (_root_.AlgebraicGeometry.Scheme.LocalRing.GenericFiber.baseMap R F) :=
  pullback.lift (pullback.fst πX
      (_root_.AlgebraicGeometry.Scheme.LocalRing.GenericFiber.baseMap R F) ≫ f)
    (pullback.snd πX (_root_.AlgebraicGeometry.Scheme.LocalRing.GenericFiber.baseMap R F))
    (by rw [Category.assoc, hf, pullback.condition])

end AlgebraicGeometry.Scheme.Pullback.GenericRestriction
