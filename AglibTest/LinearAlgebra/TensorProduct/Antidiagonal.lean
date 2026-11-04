/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.TensorProduct.Antidiagonal

/-! Axiom guard for the original comparison. -/

open TensorProduct

/--
info: 'TensorProduct.tensorBasisAntidiagonalEquiv_lof'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tensorBasisAntidiagonalEquiv_lof
