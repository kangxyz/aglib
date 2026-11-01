/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.Surjective

/-! # Dimension bounds without Noetherian or finite-dimensional assumptions -/

@[expose] public section

open TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y]

example (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f)
    (hs : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_isClosedMap_of_surjective f hf hc hs

/--
info: 'TopologicalSpace.topologicalKrullDim_le_of_isClosedMap_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.topologicalKrullDim_le_of_isClosedMap_of_surjective
