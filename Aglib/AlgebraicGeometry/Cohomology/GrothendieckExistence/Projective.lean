/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProjectiveSpaceEffectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction

/-!
# Coherent Grothendieck existence for an actual projective embedding

For a closed subscheme of finite-dimensional projective space over a complete
Noetherian ring, the native coherent completion functor is an equivalence.
Local Noetherianity of the source and properness of its structural morphism
follow from the given closed embedding; neither is an additional premise.
Effectivity descends from projective space along the original closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (A : Type u) [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A (ULift.{u} (Fin (n + 1))))
  [IsClosedImmersion i]

/-- Every coherent adic system on an actual closed projective subscheme is
in the essential image of its original coherent completion functor. -/
theorem projective_completion_essImage :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    ∀ F : AdicSystem X (idealThickeningIdealSheaf
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I),
    (completionFunctor X (idealThickeningIdealSheaf
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I)).essImage F := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  intro F
  let := (projectiveSpaceCompletionIsEquivalence A (ULift.{u} (Fin (n + 1))) I n
    (Equiv.ulift)).essSurj
  let := completionFunctor_essSurj_of_closedImmersion I i
    (toSpec A (ULift.{u} (Fin (n + 1))))
  exact Functor.EssSurj.mem_essImage _ F

/-- Coherent completion is an equivalence for a genuine projective embedding,
without any auxiliary realization, vanishing or presentation assumptions. -/
theorem projectiveCompletionIsEquivalence :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    (completionFunctor X (idealThickeningIdealSheaf
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I)).IsEquivalence := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  exact {
    faithful := (completionFunctorFullyFaithful I
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1))))).faithful
    full := (completionFunctorFullyFaithful I
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1))))).full
    essSurj := ⟨fun F => projective_completion_essImage A I n i F⟩ }

/-- Coherent Grothendieck existence for a closed projective subscheme over a
complete Noetherian base, with its original completion as forward functor. -/
def projectiveCompletionEquivalence :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    X.CoherentSheaf ≌ AdicSystem X (idealThickeningIdealSheaf
      (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  let := projectiveCompletionIsEquivalence A I n i
  exact (completionFunctor X (idealThickeningIdealSheaf
    (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I)).asEquivalence

/-- The forward functor is literally the native coherent completion. -/
theorem projectiveCompletionEquivalence_functor :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    (projectiveCompletionEquivalence A I n i).functor =
      completionFunctor X (idealThickeningIdealSheaf
        (i ≫ toSpec A (ULift.{u} (Fin (n + 1)))) I) := rfl

end AlgebraicGeometry.Scheme.Cohomology
