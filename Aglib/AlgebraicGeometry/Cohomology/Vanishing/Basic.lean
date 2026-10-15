/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension

/-!
# Noetherian Zariski vanishing statement

This is the actual scheme-parameterized all-abelian-sheaf vanishing family,
with an explicit finite topological dimension bound. Its proof is in
Vanishing.Noetherian. It imposes no properness, quasicoherence or finiteness
of coefficients and is independent of proper coherent finiteness.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Properties` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Only NoetherianSheafCohomologyVanishing with its
  original scheme/Ext universe and conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
open TopologicalSpace
/-- The assertion that Zariski cohomology of every abelian sheaf on a Noetherian scheme vanishes
in degrees above a given bound on its topological Krull dimension. -/
def NoetherianSheafCohomologyVanishing : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X]
    (M : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d n : ℕ),
    topologicalKrullDim X ≤ d → d < n → Subsingleton (Sheaf.H M n)
end AlgebraicGeometry.Scheme.Cohomology
