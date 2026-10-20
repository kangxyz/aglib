/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Aglib.Algebra.Homology.ShortComplex.ProductSequence

/-!
# Vanishing for binary products of scheme modules

In every nonnegative degree, module cohomology of a binary product is
subsingleton when both factor cohomologies are subsingleton. The exact
product sequence and structural field action are the original ones; the
scheme and module sheaves are arbitrary.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurves.ProjectiveLine`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Modules.Products` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b7211043cbc0bda1f6671273028f00b3edc96c8b115d5c93e1d5829b7897e2d4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
universe u v
namespace AlgebraicGeometry.Scheme.Cohomology
variable {K : Type u} [Field K]
open _root_.AlgebraicGeometry.Scheme.Cohomology (moduleCohomology moduleCohomologyMap_exact)
/-- Actual module cohomology of a binary product is zero when that of each factor is zero. -/
theorem moduleCohomology_prod_subsingleton (X : FScheme K)
    (M N : X.left.Modules) (n : ℕ)
    [Subsingleton (moduleCohomology K X M n)]
    [Subsingleton (moduleCohomology K X N n)] :
    Subsingleton (moduleCohomology K X (M ⨯ N) n) := by
  let S := ShortComplex.productSequence (𝟙 M) (0 : M ⟶ N)
    (0 : M ⟶ N) (𝟙 N) (by simp)
  have hS : S.ShortExact := ShortComplex.productSequence_shortExact _ _ _ _ _
  let : Subsingleton (moduleCohomology K X S.X₁ n) := inferInstanceAs
    (Subsingleton (moduleCohomology K X M n))
  let : Subsingleton (moduleCohomology K X S.X₃ n) := inferInstanceAs
    (Subsingleton (moduleCohomology K X N n))
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := (moduleCohomologyMap_exact X S hS n x).mp (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm


end AlgebraicGeometry.Scheme.Cohomology
