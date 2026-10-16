/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison

/-!
# Standard projective Cech cohomology and actual sheaf cohomology

The standard coordinate cover of polynomial projective space computes the original `Sheaf.H`
of every quasicoherent module sheaf in every positive degree. This is the existing canonical
Cech comparison, specialized to the proved coordinate cover. Its coefficient naturality is
retained. The coordinate type and the commutative coefficient ring are arbitrary.

The complex is the native full-tuple Cech complex; no boundedness or finite generation of its
terms is asserted, even when there are finitely many coordinates.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The standard coordinate cover computes the actual positive-degree cohomology of every
quasicoherent module on polynomial projective space. -/
def projectiveCechCohomologyAddEquiv (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    ((additiveCechFunctor (ProjectiveSpace R ι) (coordinateOpen R ι)).obj
      (moduleAddSheaf (ProjectiveSpace R ι) M)).homology (n + 1) ≃+
        Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) (n + 1) :=
  moduleAffineCechCohomologyAddEquiv (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)
    (isAffineOpen_coordinateOpen R ι) M
      (injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) M)) n

/-- The projective comparison preserves the actual coefficient map on `Sheaf.H`. -/
theorem projectiveCechCohomologyAddEquiv_naturality
    {M N : (ProjectiveSpace R ι).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : moduleAddSheaf (ProjectiveSpace R ι) M ⟶ moduleAddSheaf (ProjectiveSpace R ι) N)
    (n : ℕ)
    (x : ((additiveCechFunctor (ProjectiveSpace R ι) (coordinateOpen R ι)).obj
      (moduleAddSheaf (ProjectiveSpace R ι) M)).homology (n + 1)) :
    projectiveCechCohomologyAddEquiv R ι N n
      (HomologicalComplex.homologyMap
        ((additiveCechFunctor (ProjectiveSpace R ι) (coordinateOpen R ι)).map f) (n + 1) x) =
      Sheaf.H.map f (n + 1) (projectiveCechCohomologyAddEquiv R ι M n x) := by
  let I := injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) M)
  let J := injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) N)
  let φ : InjectiveResolution.Hom I J f :=
    ⟨InjectiveResolution.desc f J I, by simp⟩
  unfold projectiveCechCohomologyAddEquiv moduleAffineCechCohomologyAddEquiv
  exact moduleCechCohomologyAddEquiv_naturality (coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) _ φ n x

end AlgebraicGeometry.Scheme.Cohomology
