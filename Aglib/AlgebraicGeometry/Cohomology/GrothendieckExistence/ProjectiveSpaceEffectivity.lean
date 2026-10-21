/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProjectiveEffectivityOfRealization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRelationRealization

/-!
# Coherent completion equivalence on polynomial projective space

Actual coherent realizations of the formal graded coefficient and the
ordinary graded relations discharge both temporary realization inputs.
Uniform Serre vanishing, compatible negative-twist lifting, finite-stage
nilpotent generation and original-map full faithfulness then algebraize
the formal coefficient as an algebraic cokernel.

The forward equivalence functor is exactly the native coherent completion.
This file treats polynomial projective space; reduction from an arbitrary
closed projective subscheme is a separate required geometric step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (A : Type u) [CommRing A] [IsNoetherianRing A]
  (ι : Type u) [Finite ι] (I : Ideal A) [IsAdicComplete I A]
  (n : ℕ) (e : ι ≃ Fin (n + 1))

include n e in
/-- Every coherent adic system on polynomial projective space is the native
completion of a coherent algebraic coefficient. All graded realization,
vanishing, generator and relation-bound inputs have been proved upstream. -/
theorem projectiveSpace_completion_essImage
    (F : AdicSystem (ProjectiveSpace A ι)
      (idealThickeningIdealSheaf (toSpec A ι) I)) :
    (completionFunctor (ProjectiveSpace A ι)
      (idealThickeningIdealSheaf (toSpec A ι) I)).essImage F := by
  let : CompactSpace (ProjectiveSpace A ι) :=
    QuasiCompact.compactSpace_of_compactSpace (toSpec A ι)
  apply completion_essImage_of_projective_graded_realizations A ι I n e F
  · exact exists_formalGradedRealization (toSpec A ι) I F
  · intro P π _
    exact exists_formalGradedRelationRealization (toSpec A ι) I π

include n e in
/-- The original completion functor is full, faithful and essentially
surjective on polynomial projective space over a complete Noetherian base. -/
theorem projectiveSpaceCompletionIsEquivalence :
    (completionFunctor (ProjectiveSpace A ι)
      (idealThickeningIdealSheaf (toSpec A ι) I)).IsEquivalence where
  faithful := (completionFunctorFullyFaithful I (toSpec A ι)).faithful
  full := (completionFunctorFullyFaithful I (toSpec A ι)).full
  essSurj := ⟨fun F => projectiveSpace_completion_essImage A ι I n e F⟩

/-- Coherent Grothendieck existence on polynomial projective space, with
forward functor the original completion, not a transported replacement. -/
def projectiveSpaceCompletionEquivalence :
    (ProjectiveSpace A ι).CoherentSheaf ≌
      AdicSystem (ProjectiveSpace A ι) (idealThickeningIdealSheaf (toSpec A ι) I) := by
  let := projectiveSpaceCompletionIsEquivalence A ι I n e
  exact (completionFunctor (ProjectiveSpace A ι)
    (idealThickeningIdealSheaf (toSpec A ι) I)).asEquivalence

/-- The equivalence retains the native forward completion functor literally. -/
theorem projectiveSpaceCompletionEquivalence_functor :
    (projectiveSpaceCompletionEquivalence A ι I n e).functor =
      completionFunctor (ProjectiveSpace A ι)
        (idealThickeningIdealSheaf (toSpec A ι) I) := rfl

end AlgebraicGeometry.Scheme.Cohomology
