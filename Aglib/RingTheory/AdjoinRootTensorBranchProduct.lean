/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootBranchProduct

/-! The full scalar tensor decomposition, with literal old-root coordinate maps. -/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- All generic scalar branches form the original scalar tensor product. -/
def tensorBranchProductEquiv (p : k[X]) (hp : p.Monic) (hs : p.Separable) :
    L ⊗[k] AdjoinRoot p ≃ₐ[L]
      ∀ q : IrreducibleBranch (p.map (algebraMap k L)), AdjoinRoot q.val.val :=
  (scalarExtensionEquiv p).trans
    (branchProductEquiv (p.map (algebraMap k L)) (hp.map _) hs.map.squarefree)

/-- The old field enters each component through its actual divisor quotient map. -/
theorem tensorBranchProductEquiv_tmul_one (p : k[X]) [Fact (Irreducible p)]
    (hp : p.Monic) (hs : p.Separable)
    (a : AdjoinRoot p) (q : IrreducibleBranch (p.map (algebraMap k L))) :
    tensorBranchProductEquiv p hp hs (1 ⊗ₜ[k] a) q =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k L) p q.val.val q.property a := by
  simp only [tensorBranchProductEquiv, AlgEquiv.trans_apply]
  rw [branchProductEquiv_apply]
  have h := RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (L := L) p) a
  change scalarExtensionEquiv p (1 ⊗ₜ[k] a) = scalarMap (algebraMap k L) p a at h
  rw [h]
  exact RingHom.congr_fun (divisorMap_comp_scalarMap (algebraMap k L) p q.val.val q.property) a

end AdjoinRoot
