/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Aglib.Algebra.Homology.CochainComplex.OppositeQuasiIso


/-!
# Bounded-above projective replacements

Negating degrees and passing to the opposite category turns the actual
bounded-below injective replacement into a bounded-above projective replacement.
The upper bound is unchanged. Quasi-isomorphisms are transported through the
actual reindexing and opposite functors, rather than assumed preserved.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Algebra/Homology/BoundedProjectiveReplacement.lean`.
SHA-256: `d96784939a3db2e27c7fdf0e0875853c13bfee1c8c4af84fdcfb5b803e446f8c`.
Selected source lines: 1–80.
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

/-- A bounded-above complex in an abelian category with enough projectives has
an actual bounded-above degreewise-projective quasi-isomorphic replacement. -/
theorem exists_boundedAbove_projective_replacement [EnoughProjectives C]
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex C ℤ) (p : P ⟶ K), QuasiIso p ∧
      (∀ n, Projective (P.X n)) ∧ P.IsStrictlyLE b := by
  let E := CochainComplex.opEquivalence C
  let KO := E.functor.obj (op K)
  have : KO.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (K.isZero_of_isStrictlyLE b (-n) (by omega)).op
  obtain ⟨L, i, hi, hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective KO (-b)
  let P := (E.inverse.obj L).unop
  let p : P ⟶ K := (E.inverse.map i).unop ≫ (E.unitIso.app (op K)).hom.unop
  refine ⟨P, p, ?_, ?_, ?_⟩
  · dsimp [p, E]
    infer_instance
  · intro n
    exact inferInstanceAs (Projective ((L.X (-n)).unop))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (L.isZero_of_isStrictlyGE (-b) (-n) (by omega)).unop

end CochainComplex
