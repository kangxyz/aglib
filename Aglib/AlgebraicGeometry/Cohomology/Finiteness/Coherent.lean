/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# General coherent finiteness and Zariski cohomological dimension

ProperModuleCohomologyFinite is the all-field, all-module, all-degree
specialization of Stacks 02O6 (30.19.2). The actual finitely presented module
sheaf is quasi-coherent and coherent on the proper Noetherian field scheme;
that identification with the source hypotheses is part of this retained
standard family. Both its Hn and field action are constructed in Modules.
Finite local bases imply finite presentation below by an actual presentation.

The proper finiteness family is an explicit hypothesis, not a newly declared axiom.
Source statements and correction comments inspected 2026-10-09.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Properties` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module provides general scheme cohomology interfaces.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u

theorem finitePresentation_of_finite_local_basis (X : Scheme.{u}) (M : X.Modules)
    (q : M.LocalGeneratorsData.{u}) [q.IsLocallyFreeData]
    [∀ i, Finite (q.generators i).I] : M.IsFinitePresentation := by
  refine { exists_quasicoherentData := ⟨q.quasiCoherentData, ?_⟩ }
  constructor
  intro i
  constructor
  · constructor
    exact inferInstanceAs (Finite (q.generators i).I)
  · constructor
    exact inferInstanceAs (Finite (ULift Empty))

/-- The explicit input asserting finiteness in every nonnegative cohomology degree for finitely
presented module sheaves on proper field schemes, uniformly over all fields. -/
def ProperModuleCohomologyFinite : Prop :=
  ∀ (K : Type u) [Field K] (X : FScheme K) (M : X.left.Modules) (n : ℕ),
    IsProper X.hom → M.IsFinitePresentation → Module.Finite K (moduleCohomology K X M n)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
open Opposite
variable {K : Type u} [Field K]
theorem moduleGlobalSections_finrank (X : FScheme K) (M : X.left.Modules) :
    Module.finrank K (M.val.obj (op ⊤)) = Module.finrank K (moduleCohomology K X M 0) :=
  (moduleH0Equiv X M).finrank_eq.symm

theorem moduleGlobalSections_finite (hfinite : ProperModuleCohomologyFinite.{u})
    (X : FScheme K) (M : X.left.Modules) (hX : IsProper X.hom) (hM : M.IsFinitePresentation) :
    Module.Finite K (M.val.obj (op ⊤)) := by
  let := hfinite K X M 0 hX hM
  exact Module.Finite.of_surjective (moduleH0Equiv X M).toLinearMap (moduleH0Equiv X M).surjective
end AlgebraicGeometry.Scheme.Cohomology
