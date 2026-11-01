/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.IrreducibleClosed

/-! Closed-subspace dimension uses the original induced topology, without separation hypotheses. -/

@[expose] public noncomputable section

open TopologicalSpace

example {X : Type*} [TopologicalSpace X] (Z : IrreducibleCloseds X) :
    topologicalKrullDim Z = (Order.height Z : WithBot ℕ∞) :=
  topologicalKrullDim_irreducibleClosed_eq_height Z

example {X : Type*} [TopologicalSpace X] (d : ℕ)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ Z : IrreducibleCloseds X, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z :=
  exists_irreducibleClosed_topologicalKrullDim_ge d hd

example {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsClosed S) (d : ℕ)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim S) :
    ∃ Z : IrreducibleCloseds X, (Z : Set X) ⊆ S ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim Z :=
  exists_irreducibleClosed_subset_topologicalKrullDim_ge S hS d hd

end
