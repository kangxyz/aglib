/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwistLifting
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompatiblePresentation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalGeneration
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Coherent

/-!
# An actual formal epimorphism from fixed algebraic negative twists

The sole geometric premise is one bound killing first cohomology of all
successive twisted kernels. Given that bound, this file constructs an actual
morphism from the completion of a fixed finite sum of negative twists and
proves every component epic. The associated-graded geometric realization
must discharge the bound before the projective existence endpoint.
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
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (ι : Type u) [Finite ι]

/-- The original finite coproduct of one negative twist, bundled only with
its proved coherence certificate. -/
def finiteNegativeTwistCoefficient (J : Type u) [Finite J] (d : ℕ) :
    (ProjectiveSpace A ι).CoherentSheaf :=
  ⟨∐ fun _ : J => twistingSheaf A ι (-(d : ℤ)),
    twistingCoproduct_affineLocallyFiniteType A ι (fun _ : J => -(d : ℤ))⟩

/-- One uniform kernel H¹ bound gives an actual componentwise epimorphism
from completion of a fixed finite algebraic negative-twist coefficient.
The stage-zero convention and arbitrary Noetherian base rings are retained. -/
theorem exists_completion_negativeTwist_epi_of_uniform_h1
    (I : Ideal A)
    (F : AdicSystem (ProjectiveSpace A ι)
      (idealThickeningIdealSheaf (toSpec A ι) I))
    (B : ℕ)
    (hK : ∀ d : ℕ, B ≤ d → ∀ n, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι (d : ℤ))).obj
          (kernel (F.transition n)))) 1)) :
    ∃ d : ℕ, B ≤ d ∧ ∃ (J : Type u) (_ : Finite J)
      (p : (completionFunctor (ProjectiveSpace A ι)
        (idealThickeningIdealSheaf (toSpec A ι) I)).obj
          (finiteNegativeTwistCoefficient A ι J d) ⟶ F),
      ∀ n : ℕ, Epi (p.hom.app (op n)) := by
  obtain ⟨d, hd, J, hJ, p, hp⟩ :=
    exists_compatible_negativeTwist_generators_of_uniform_h1 A ι F.obj 1
      (F.property.coherent 1) (fun n => F.transition_epi n) B hK
  let := hJ
  let P := finiteNegativeTwistCoefficient A ι J d
  let : (∐ fun _ : J => twistingSheaf A ι (-(d : ℤ))).IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent A ι (fun _ : J => -(d : ℤ))
  let := hp
  let q := completionDesc (idealThickeningIdealSheaf (toSpec A ι) I) P F p
  refine ⟨d, hd, J, hJ, q, ?_⟩
  intro n
  let : Epi (p.app (op n)) := formal_compatible_epi_of_special_fibre
    (toSpec A ι) I F p n
  exact compatibleQuotientDesc_app_epi
    (idealThickeningIdealSheaf (toSpec A ι) I) F.property.annihilated p (op n)

end AlgebraicGeometry.Scheme.Cohomology
