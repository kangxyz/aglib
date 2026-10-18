/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches

/-!
# The literal finite product of all squarefree polynomial branches

The native reduced Artinian decomposition is reindexed by the existing actual
irreducible branches. Each component is exactly the original divisor quotient
map. This is an algebraic decomposition, with no norm or transfer assertion.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k]

/-- Every branch of a monic polynomial belongs to a finite actual indexing type. -/
theorem finite_irreducibleBranch (p : k[X]) (hp : p.Monic) :
    Finite (IrreducibleBranch p) := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  exact Finite.of_equiv (MaximalSpectrum (AdjoinRoot p))
    (branchEquivMaximal p hp.ne_zero).symm

/-- The original squarefree quotient algebra is the product of all its actual
irreducible branch fields, with no branch selected or omitted. -/
def branchProductEquiv (p : k[X]) (hp : p.Monic) (hs : Squarefree p) :
    AdjoinRoot p ≃ₐ[k] ∀ q : IrreducibleBranch p, AdjoinRoot q.val.val := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : IsReduced (AdjoinRoot p) := isReduced_of_squarefree p hs
  exact ((IsArtinianRing.equivPi (AdjoinRoot p)).restrictScalars k).trans
    ((AlgEquiv.piCongrLeft k (fun m : MaximalSpectrum (AdjoinRoot p) =>
      AdjoinRoot p ⧸ m.asIdeal) (branchEquivMaximal p hp.ne_zero)).symm.trans
      (AlgEquiv.piCongrRight fun q => branchQuotientAlgEquiv p q))

/-- Each product coordinate is the literal original branch quotient map. -/
theorem branchProductEquiv_apply (p : k[X]) (hp : p.Monic) (hs : Squarefree p)
    (a : AdjoinRoot p) (q : IrreducibleBranch p) :
    branchProductEquiv p hp hs a q = divisorMap p q.val.val q.property a := by
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : IsReduced (AdjoinRoot p) := isReduced_of_squarefree p hs
  change branchQuotientEquiv p q
    (IsArtinianRing.equivPi (AdjoinRoot p) a (branchMaximal p q)) = _
  rw [IsArtinianRing.equivPi_apply, branchQuotientEquiv_mk]

/-- Polynomial representatives keep exactly their original residue classes in every branch. -/
theorem branchProductEquiv_mk (p : k[X]) (hp : p.Monic) (hs : Squarefree p)
    (a : k[X]) (q : IrreducibleBranch p) :
    branchProductEquiv p hp hs (mk p a) q = mk q.val.val a := by
  rw [branchProductEquiv_apply, divisorMap_mk]

end AdjoinRoot
