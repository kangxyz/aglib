/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Fibers
public import Aglib.Algebra.Homology.Semicontinuity

/-!
# Upper semicontinuity on the same actual finite-cover model

The same literal residue-field scalar extension computes unchanged ordinary
fibre cohomology. Native finite-complex semicontinuity therefore applies to
its original dimension function. The model-level theorem uses the actual
cover and comparison, with no additional Noetherian or reducedness premise.
Projective and proper suppliers construct this same model internally.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module AlgebraicGeometry
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}} [X.IsSeparated]
    {U : ι → X.Opens}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Every original fibre-cohomology dimension is upper semicontinuous for the displayed
actual universal model. The model itself need not be constructed again for each point. -/
theorem FiniteCechCohomologyModel.upperSemicontinuous_fiberCohomologyDimension
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
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
    exact (D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q p).symm
  rw [he] at h
  exact h

end AlgebraicGeometry.Scheme.Cohomology
