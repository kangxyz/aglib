/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# A specified dense algebraic-closure embedding

Source: `R5Lab.Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.Witness`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

namespace AlgebraicClosure
universe u

/-- A specified dense embedding of the actual algebraic closure extending the base map.
This predicate supplies only the embedding, its extension equation, and density.
Completeness, algebraic closedness, norm compatibility, and isometry of a target
are separate assumptions or separately proved results. No norm on the source
algebraic closure is implicit in this predicate. -/
def DenseEmbeddingExtends {F K : Type u} [Field F] [NormedField K]
    (f : F →+* K) : Prop :=
  ∃ i : AlgebraicClosure F →+* K,
    i.comp (algebraMap F (AlgebraicClosure F)) = f ∧ DenseRange i

end AlgebraicClosure
