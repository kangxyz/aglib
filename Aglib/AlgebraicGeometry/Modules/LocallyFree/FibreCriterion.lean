/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Geometric-fibre detection for finite locally free module maps

This optional all-scheme, all-rank family concerns the actual canonical
module-sheaf pullback of an independently given map. It is a disclosed
corollary of Stacks 00DV, Lemma 10.20.1(6), and 089Q, Lemma 17.14.5.
Geometric-fibre isomorphisms descend through the faithful field extension
of each residue field, then Nakayama gives stalk surjectivity and equal local
ranks; local finite free presentations and 089Q give the isomorphism.
The retained realization includes identifying actual scheme-module pullback
at a field point with the stalk tensor product. These bridges are part of
this general source corollary, not claimed as previously formalized lemmas.
All bases, including nonreduced and non-Noetherian schemes, are allowed;
empty schemes satisfy the criterion vacuously. Source statements and visible
correction records were inspected on 2026-10-09. No curve, degree, graph,
evaluation, section or Abel conclusion is supplied by this family.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.LocallyFree.FibreCriterion` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`97768675ebf6532c5616916ed084a7dfad42b44cf55c4a6306dc3679d738fa1f`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
def FiniteLocallyFreeGeometricIso : Prop :=
  ∀ (X : Scheme.{u}) (M N : X.Modules) (φ : M ⟶ N),
    M.IsLocallyFree → M.IsFinitePresentation → N.IsLocallyFree → N.IsFinitePresentation →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ X),
      IsIso ((Scheme.Modules.pullback p).map φ)) → IsIso φ
end AlgebraicGeometry.Scheme.Modules
