/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero

/-!
# Structural-ring Cech comparison for actual projective twists

The standard coordinate Cech complex of the constructed `O(d)` computes the original
`Sheaf.H` in every degree, linearly over the coefficient ring. Its scalar map is exactly the
one induced by the actual projective structure morphism and the Gamma-Spec isomorphism.
This is a comparison with the unchanged full-tuple Cech complex; no twist cohomology
calculation or boundedness assertion is included.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Standard-cover Cech cohomology of the actual `O(d)` is the original `Sheaf.H`, linearly
for the coefficient action from the original projective structure morphism. -/
def twistingCechCohomologyLinearEquiv (d : ℤ) (n : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (ProjectiveSpace.toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) (n + 1)
    (moduleCechComplex (ProjectiveSpace R ι) α (twistingSheaf R ι d)
      (coordinateOpen R ι)).homology (n + 1) ≃ₗ[R]
        Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) (n + 1) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (ProjectiveSpace.toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) (n + 1)
  exact moduleAffineCechCohomologyLinearEquiv (ProjectiveSpace R ι) α
    (twistingSheaf R ι d) (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)
    (injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d))) n
    (isAffineOpen_coordinateOpen R ι)

/-- The actual standard-cover Cech complex of every integer twist computes the original
`Sheaf.H` in all nonnegative degrees, with its original structural-ring action. -/
def twistingCechCohomologyLinearEquivAll (d : ℤ) (n : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (ProjectiveSpace.toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
    (moduleCechComplex (ProjectiveSpace R ι) α (twistingSheaf R ι d)
      (coordinateOpen R ι)).homology n ≃ₗ[R]
        Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) n := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (ProjectiveSpace.toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  cases n with
  | zero =>
    exact moduleCechCohomologyLinearEquivZero (ProjectiveSpace R ι) α
      (twistingSheaf R ι d) (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)
  | succ n => exact twistingCechCohomologyLinearEquiv R ι d n

end AlgebraicGeometry.Scheme.Cohomology
