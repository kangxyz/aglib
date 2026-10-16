/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Fibers

/-!
# Original fibre dimensions on a constructed projective model

The actual residue-field scalar extension of the same finite-projective
model computes original ordinary fibre cohomology with its literal
structural residue-field action. This pointwise numerical comparison is
shared by semicontinuity, Euler characteristic and Grauert criteria.
It neither assumes nor concludes degreewise homology base-change exactness.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- The original fibre dimension agrees with the homology dimension of the literal
residue-field scalar extension of the constructed model. -/
theorem ProjectiveCohomologyModel.fiberCohomologyDimension_eq_finrank
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)
    (q : ℕ) (p : PrimeSpectrum R) :
    moduleFiberCohomologyDimension f M q p = finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj D.complex).homology (q : ℤ)) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.fiberCohomologyDimension_eq_finrank D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat q p

end AlgebraicGeometry.Scheme.Cohomology
