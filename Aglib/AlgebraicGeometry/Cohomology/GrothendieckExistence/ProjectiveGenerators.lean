/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedRealization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RealizationVanishing
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ProjectivePresentation

/-!
# Algebraic negative-twist generators of arbitrary projective formal systems

The actual coherent associated-graded realization supplies one uniform Serre
bound. Its original component splittings give compatible lifts of finitely
many special-fibre generators, and nilpotent generation proves an epimorphism
at every formal level. No realization, vanishing, or generator premise is
assumed in this interface. This constructs a formal cover, not by itself an
algebraization of the target coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (A : Type u) [CommRing A] [IsNoetherianRing A]
  (ι : Type u) [Finite ι] (I : Ideal A)
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (F : AdicSystem (ProjectiveSpace A ι)
    (idealThickeningIdealSheaf (toSpec A ι) I))

include n e in
/-- Actual coherent graded realization yields one uniform H¹ bound for all
successive kernels of an arbitrary projective formal coherent coefficient. -/
theorem projective_formal_uniform_h1 :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ k : ℕ,
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).obj
          (kernel (F.transition k)))) 1) := by
  let : CompactSpace (ProjectiveSpace A ι) :=
    QuasiCompact.compactSpace_of_compactSpace (toSpec A ι)
  obtain ⟨G, ⟨eG⟩⟩ := exists_formalGradedRealization (toSpec A ι) I F
  exact projective_uniform_h1_of_realized_coproduct
    (algebraMap A I.associatedGraded) ι n e F.gradedPiece G.obj G.property eG

include n e in
/-- Every projective formal coherent coefficient admits an actual
componentwise epimorphism from completion of one fixed finite sum of
algebraic negative twists. No uniform-vanishing assumption remains. -/
theorem exists_completion_negativeTwist_epi :
    ∃ (d : ℕ) (J : Type u) (_ : Finite J)
      (p : (completionFunctor (ProjectiveSpace A ι)
        (idealThickeningIdealSheaf (toSpec A ι) I)).obj
          (finiteNegativeTwistCoefficient A ι J d) ⟶ F),
      ∀ k : ℕ, Epi (p.hom.app (op k)) := by
  obtain ⟨B, hB⟩ := projective_formal_uniform_h1 A ι I n e F
  obtain ⟨d, _, J, hJ, p, hp⟩ :=
    exists_completion_negativeTwist_epi_of_uniform_h1 A ι I F B hB
  exact ⟨d, J, hJ, p, hp⟩

end AlgebraicGeometry.Scheme.Cohomology
