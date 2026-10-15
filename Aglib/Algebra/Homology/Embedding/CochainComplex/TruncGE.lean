/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedBelowComparison.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256: `8fc2ddec29ee432d99f89dd2ef79a0149db1506a0190d7a7ff5db5db85a11a58`.
Selected declaration ranges: [[117, 125]].
Actual maps and premises are preserved; the generic truncation lift is recorded explicitly.
-/

/-! # Factorization through good lower truncation

A map into a complex with a strict lower term bound factors through the
source's good lower truncation. The original module-sheaf statement on a scheme
is the specialization `A := X.Modules`; the bound and the actual maps are retained.
-/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A map into a strictly lower-bounded target factors through good truncation. -/
def fromTruncGE {K L : CochainComplex A ℤ} (f : L ⟶ K) (a : ℤ)
    [K.IsStrictlyGE a] : L.truncGE a ⟶ K :=
  CochainComplex.truncGEMap f a ≫ inv (K.πTruncGE a)

lemma πTruncGE_fromTruncGE {K L : CochainComplex A ℤ} (f : L ⟶ K) (a : ℤ)
    [K.IsStrictlyGE a] : L.πTruncGE a ≫ fromTruncGE f a = f := by
  dsimp only [fromTruncGE]
  rw [← Category.assoc, CochainComplex.πTruncGE_naturality,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CochainComplex
