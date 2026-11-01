/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.ClosedEmbedding

/-! # Generic codimension one without catenarity or Noetherianity -/

@[expose] public section

open TopologicalSpace Topology

attribute [local instance] specializationOrder

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [T0Space X] [IrreducibleSpace X]
    [QuasiSober Y] [T0Space Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : IsClosedEmbedding f) (n : ℕ)
    (hX : topologicalKrullDim X = n)
    (hY : topologicalKrullDim Y ≤ (n : WithBot ℕ∞) + 1)
    (hrange : Set.range f ≠ Set.univ) : Order.coheight (f (genericPoint X)) = 1 :=
  coheight_image_genericPoint_eq_one f hf n hX hY hrange

/--
info: 'TopologicalSpace.coheight_image_genericPoint_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.coheight_image_genericPoint_eq_one
