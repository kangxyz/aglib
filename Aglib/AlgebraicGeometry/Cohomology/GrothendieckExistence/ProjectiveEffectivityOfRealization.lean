/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RealizationVanishing
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationPresentation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationDiagramGraded
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.PresentationAlgebraization
public import Aglib.RingTheory.AssociatedGraded.Basic

/-!
# Projective presentation assembly from explicit graded realizations

This is a conditional integration theorem, not unconditional projective
Grothendieck existence. Its named temporary inputs assert genuine coherent
realizations of the original formal and relation graded coproducts on the
actual base-change space. They are to be instantiated with the geometric
realization theorems, not retained in the public existence endpoint.

No uniform vanishing bound, finite kernel bound, presentation or effectivity
assumption remains beyond these explicitly displayed realization inputs.
The conclusion is the essential image of the original completion functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (A : Type u) [CommRing A] [IsNoetherianRing A]
  (ι : Type u) [Finite ι] (I : Ideal A) [IsAdicComplete I A]

local notation "Y" => pullback (toSpec A ι)
  (Spec.map (CommRingCat.ofHom (algebraMap A I.associatedGraded)))
local notation "pY" => pullback.fst (toSpec A ι)
  (Spec.map (CommRingCat.ofHom (algebraMap A I.associatedGraded)))
local notation "K" => idealThickeningIdealSheaf (toSpec A ι) I

/-- Conditional assembly from actual coherent graded realizations. The
first temporary input concerns the arbitrary given formal system. The second
concerns the original relation kernels of any algebraic-coefficient cover.
Both are explicitly required here and must be proved by the geometric
realization construction before claiming projective existence. -/
theorem completion_essImage_of_projective_graded_realizations
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : AdicSystem (ProjectiveSpace A ι) K)
    (realizeFormal : ∃ G : (Y).CoherentSheaf,
      Nonempty ((pushforward pY).obj G.obj ≅ F.gradedUnderlying))
    (realizeRelations : ∀ (P : (ProjectiveSpace A ι).CoherentSheaf)
      (π : (completionFunctor (ProjectiveSpace A ι) K).obj P ⟶ F),
      (∀ k : ℕ, Epi (π.hom.app (op k))) → ∃ G : (Y).CoherentSheaf,
        Nonempty ((pushforward pY).obj G.obj ≅ ∐ relationGradedPiece π)) :
    (completionFunctor (ProjectiveSpace A ι) K).essImage F := by
  obtain ⟨G, ⟨eG⟩⟩ := realizeFormal
  obtain ⟨B, hB⟩ := projective_uniform_h1_of_realized_coproduct
    (algebraMap A I.associatedGraded) ι n e F.gradedPiece G.obj G.property eG
  obtain ⟨d, _, J, hJ, π, hπ⟩ :=
    exists_completion_negativeTwist_epi_of_uniform_h1 A ι I F B hB
  let := hJ
  let P := finiteNegativeTwistCoefficient A ι J d
  obtain ⟨G', ⟨eG'⟩⟩ := realizeRelations P π hπ
  obtain ⟨C, hC⟩ := projective_uniform_h1_of_realized_coproduct
    (algebraMap A I.associatedGraded) ι n e (relationGradedPiece π)
      G'.obj G'.property eG'
  have hrel (d : ℕ) (hd : C ≤ d) (k : ℕ) :
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).obj
          (kernel ((relationDiagram π).map (homOfLE (Nat.le_succ k)).op)))) 1) :=
    moduleCohomology_subsingleton_of_iso
      (((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).mapIso
        (relationDiagramGradedIso π k)).symm) 1 (hC d hd k)
  obtain ⟨c, _, L, hL, r, hr⟩ :=
    exists_completion_relation_epi_of_uniform_h1 A ι I π hπ C hrel
  let := hL
  exact completion_essImage_of_coefficient_and_relation_epi I (toSpec A ι) F π hπ r hr

end AlgebraicGeometry.Scheme.Cohomology
