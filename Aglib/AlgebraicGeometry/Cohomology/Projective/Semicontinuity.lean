/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Fibers
public import Aglib.Algebra.Homology.Semicontinuity

/-!
# Upper semicontinuity of projective fibre cohomology

The constructed universal finite-projective model identifies the actual
cohomology of every residue-field fibre with the homology of its native
scalar extension. The finite-complex semicontinuity theorem therefore
applies to the original ordinary pulled coefficient and original
structural residue-field action. The geometric supplier uses an actual
projective embedding over a Noetherian ring, a coherent coefficient and
relative flatness. No base-change or finite-model family is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module AlgebraicGeometry
open HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Every original fibre-cohomology dimension is upper semicontinuous for the displayed
actual universal model. The model itself need not be constructed again for each point. -/
theorem ProjectiveCohomologyModel.upperSemicontinuous_fiberCohomologyDimension
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) :
    UpperSemicontinuous (moduleFiberCohomologyDimension f M q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  have h := upperSemicontinuous_finrank_homology_residueField_of_projective.{u, u, 0}
    D.complex (q : ℤ)
  have he : (fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj D.complex).homology (q : ℤ))) =
      moduleFiberCohomologyDimension f M q := by
    funext p
    exact (D.fiberCohomologyDimension_eq_finrank e hflat q p).symm
  rw [he] at h
  exact h

/-- Coherent relatively flat coefficients on an actual projective embedding over a
Noetherian ring have upper semicontinuous original fibre-cohomology dimension in every
degree. The finite-projective model is supplied by the proved construction. -/
theorem upperSemicontinuous_moduleFiberCohomologyDimension_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) :
    UpperSemicontinuous (moduleFiberCohomologyDimension f M q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.upperSemicontinuous_fiberCohomologyDimension e hflat q

end AlgebraicGeometry.Scheme.Cohomology
