/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# Quasi-isomorphisms under integer negation and opposite cochain equivalence

These original reindexing and opposite maps preserve quasi-isomorphisms in an arbitrary
abelian category. No upper or lower term bound is imposed.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/BoundedProjectiveReplacement.lean`.
SHA-256: `d96784939a3db2e27c7fdf0e0875853c13bfee1c8c4af84fdcfb5b803e446f8c`.
Selected source lines: 31–53.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reversing integer degrees preserves actual quasi-isomorphisms. -/
instance quasiIso_restriction_neg_up {K L : ChainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (restrictionMap f ComplexShape.embeddingUpIntDownInt) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff' _ (n-1) n (n+1) (by simp) (by simp)]
    exact (quasiIsoAt_iff' f (-(n-1)) (-n) (-(n+1)) (by simp; omega)
      (by simp; omega)).mp inferInstance

/-- The inverse integer reindexing preserves actual quasi-isomorphisms. -/
instance quasiIso_restriction_neg_down {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (restrictionMap f ComplexShape.embeddingDownIntUpInt) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff' _ (n+1) n (n-1) (by simp) (by simp)]
    exact (quasiIsoAt_iff' f (-(n+1)) (-n) (-(n-1)) (by simp; omega)
      (by simp; omega)).mp inferInstance

/-- The inverse opposite cochain equivalence preserves actual quasi-isomorphisms. -/
instance quasiIso_cochain_opEquivalence_inverse_map {K L : CochainComplex Cᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((CochainComplex.opEquivalence C).inverse.map f).unop) := by
  change QuasiIso ((HomologicalComplex.unopFunctor C (ComplexShape.down ℤ)).map
    (restrictionMap f ComplexShape.embeddingDownIntUpInt).op)
  infer_instance

end CochainComplex
