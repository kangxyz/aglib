/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Projective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Point

/-! # Actual affine effectivity over a complete Noetherian base

Projective zero-space is the original affine base. Reusing projective
Grothendieck existence therefore algebraizes its native formal systems,
without introducing a second finite-module reconstruction model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) [IsAdicComplete I R]

omit [IsNoetherianRing R] in
private theorem completionIsEquivalence_of_baseMap_eq
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : Ideal R)
    (f g : X ⟶ Spec (CommRingCat.of R)) (h : f = g)
    (hf : (completionFunctor X (idealThickeningIdealSheaf f I)).IsEquivalence) :
    (completionFunctor X (idealThickeningIdealSheaf g I)).IsEquivalence := by
  subst g
  exact hf

/-- The native affine completion functor is an equivalence over a complete base. -/
theorem affineCompleteCompletionIsEquivalence :
    (completionFunctor (Spec (CommRingCat.of R))
      (idealThickeningIdealSheaf (𝟙 (Spec (CommRingCat.of R))) I)).IsEquivalence := by
  let i := inv (toSpec R (ULift.{u} (Fin 1)))
  have h := projectiveCompletionIsEquivalence R I 0 i
  exact completionIsEquivalence_of_baseMap_eq (R := R) I
    (i ≫ toSpec R (ULift.{u} (Fin 1))) (𝟙 _)
    (IsIso.inv_hom_id _) h

/-- Every actual affine formal system over the complete base is effective. -/
theorem affineComplete_completion_essImage
    (F : AdicSystem (Spec (CommRingCat.of R))
      (idealThickeningIdealSheaf (𝟙 (Spec (CommRingCat.of R))) I)) :
    (completionFunctor (Spec (CommRingCat.of R))
      (idealThickeningIdealSheaf (𝟙 (Spec (CommRingCat.of R))) I)).essImage F := by
  let := affineCompleteCompletionIsEquivalence R I
  exact Functor.EssSurj.mem_essImage _ F

end AlgebraicGeometry.Scheme.Cohomology
