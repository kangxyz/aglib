/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.FiniteCoordinates

/-!
# The original projective twist cohomology and its finite endpoint weights

The actual `Sheaf.H` of every integer twist identifies with the native relative-simplex
homology sum on its original empty/full negative-support weights. The weight index type is
finite for finite coordinate types. Ring and coordinates retain the common geometric
universe, so a finite coordinate labeling is independent of a particular small `Fin` type.
The original cohomology is finite free in every degree and obeys the sharp positive-degree
vanishing bound `d ≥ -n`, with both possible endpoint contributions retained when `n = 0`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original twist cohomology is the native homology sum on its finite endpoint weight
set, with both empty and full negative support retained. -/
def twistingCohomologyEndpointEquiv [Finite ι] (d : ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q ≃ₗ[R]
      (Π₀ e : coordinateLaurentEndpointWeight (ι := ι) d,
        (AlgebraicTopology.RelativeSimplex.complex R
          (coordinateNegativeSupport e.val.val)).homology q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
  exact (twistingLaurentCohomologyLinearEquiv R ι d q).symm.trans
    (coordinateLaurentTupleHomologyEndpointEquiv (ι := ι) R d q)

/-- The actual cohomology of every integer twist on projective `n`-space is finite over the
original base ring. An explicit labeling preserves arbitrary ring and coordinate universes. -/
theorem twistingCohomology_finite (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
    Module.Finite R
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
  let : Module.Finite R ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) :=
    coordinateLaurentTupleHomology_finite_of_equivFin R n e d q
  exact Module.Finite.equiv (twistingLaurentCohomologyLinearEquiv R ι d q)

/-- The same original twist cohomology modules are free over every commutative base ring. -/
theorem twistingCohomology_free (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
    Module.Free R
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) q
  let : Module.Free R ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) :=
    coordinateLaurentTupleHomology_free_of_equivFin R n e d q
  exact Module.Free.of_equiv (twistingLaurentCohomologyLinearEquiv R ι d q)

/-- Original twist cohomology vanishes outside its two possible endpoint degrees. -/
theorem twistingCohomology_subsingleton_of_ne_endpoints (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q) := by
  let := ModuleCat.subsingleton_of_isZero
    (coordinateLaurentTupleHomology_isZero_of_ne_endpoints_of_equivFin R n e d q hq0 hqn)
  exact (twistingLaurentCohomologyLinearEquiv R ι d q).symm.injective.subsingleton

/-- The sharp positive-degree vanishing bound for actual projective twists: `O(d)` has
zero original cohomology in every positive degree as soon as `d ≥ -n`. -/
theorem twistingCohomology_subsingleton_of_neg_le_degree (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (q : ℕ) (hd : -(n : ℤ) ≤ d) (hq : q ≠ 0) :
    Subsingleton
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) q) := by
  let := ModuleCat.subsingleton_of_isZero
    (coordinateLaurentTupleHomology_isZero_of_neg_le_degree_of_equivFin R n e d q hd hq)
  exact (twistingLaurentCohomologyLinearEquiv R ι d q).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
