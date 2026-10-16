/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.MonomialTrace

/-!
# Perfectness of the original top Serre pairing for negative twists

The original geometric pairing is exactly the existing perfect Laurent residue pairing
under the proved original polynomial-Hom and negative-cohomology equivalences. The native
`LinearMap.IsPerfPair` conclusion therefore concerns the canonical trace after the actual
coefficient cohomology map, over every commutative ring and in every projective dimension.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The canonical geometric top pairing of any original polynomial map with any original
cohomology class is exactly the existing native perfect Laurent residue pairing. -/
theorem projectiveTopSerreMap_residuePolynomial (n : ℕ) (e : ι ≃ Fin (n + 1))
    (m : ℕ) (p : homogeneousSubmodule ι R m)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))) n) :
    projectiveTopSerreMap R ι n e
        (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))
        (residuePolynomialMultiplication R ι m p) x =
      coordinateLaurentResiduePairing R m p (residueTwistCohomologyLinearEquiv R ι n e m x) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let d : ℤ := -(m : ℤ) - (Fintype.card ι : ℤ)
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
  let H := Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) n
  let L : homogeneousSubmodule ι R m →ₗ[R] H →ₗ[R] R :=
    (projectiveTopSerreMap R ι n e (twistingSheaf R ι d)).comp
      (residuePolynomialMultiplicationLinearEquiv R ι (e.symm 0) m).toLinearMap
  let Q : homogeneousSubmodule ι R m →ₗ[R] H →ₗ[R] R :=
    (coordinateLaurentResiduePairing R m).compl₂
      (residueTwistCohomologyLinearEquiv R ι n e m).toLinearMap
  have hLQ : L = Q := by
    apply (homogeneousPieceBasis (ι := ι) R m).ext
    intro a
    apply LinearMap.ext
    intro y
    change projectiveTopSerreMap R ι n e (twistingSheaf R ι d)
        (residuePolynomialMultiplicationLinearEquiv R ι (e.symm 0) m
          (homogeneousPieceBasis R m a)) y =
      coordinateLaurentResiduePairing R m (homogeneousPieceBasis R m a)
        (residueTwistCohomologyLinearEquiv R ι n e m y)
    rw [residuePolynomialMultiplicationLinearEquiv_apply]
    obtain ⟨z, rfl⟩ := (twistingLaurentCohomologyLinearEquiv R ι d n).surjective y
    obtain ⟨c, rfl⟩ :=
      (ModuleCat.epi_iff_surjective
        ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n)).mp (by infer_instance) z
    exact projectiveTopSerreMap_residueMonomial_cycle R ι n e m a c
  have h := congrArg (fun B : homogeneousSubmodule ι R m →ₗ[R] H →ₗ[R] R => B p x) hLQ
  change projectiveTopSerreMap R ι n e (twistingSheaf R ι d)
      (residuePolynomialMultiplicationLinearEquiv R ι (e.symm 0) m p) x =
    coordinateLaurentResiduePairing R m p (residueTwistCohomologyLinearEquiv R ι n e m x) at h
  rw [residuePolynomialMultiplicationLinearEquiv_apply] at h
  exact h

/-- The canonical top Serre pairing for `O(-m-card ι)` is a native perfect pairing over
any commutative base ring, including projective dimension zero. -/
theorem projectiveTopSerreMap_residueTwist_isPerfPair (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
    (projectiveTopSerreMap R ι n e
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))).IsPerfPair := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
  apply LinearMap.IsPerfPair.congr (p := coordinateLaurentResiduePairing (ι := ι) R m)
    (residuePolynomialMultiplicationLinearEquiv R ι (e.symm 0) m).symm
    (residueTwistCohomologyLinearEquiv R ι n e m)
    (projectiveTopSerreMap R ι n e
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))))
  ext p g
  change projectiveTopSerreMap R ι n e
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))
      (residuePolynomialMultiplicationLinearEquiv R ι (e.symm 0) m p)
      ((residueTwistCohomologyLinearEquiv R ι n e m).symm g) =
    coordinateLaurentResiduePairing R m p g
  rw [residuePolynomialMultiplicationLinearEquiv_apply, projectiveTopSerreMap_residuePolynomial,
    LinearEquiv.apply_symm_apply]

/-- The original top Serre map is bijective for every displayed negative twist. -/
theorem projectiveTopSerreMap_residueTwist_bijective (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    Function.Bijective (projectiveTopSerreMap R ι n e
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
  exact (projectiveTopSerreMap_residueTwist_isPerfPair R ι n e m).bijective_left

/-- The native perfect-pairing equivalence for the original negative-twist top Serre map. -/
def residueTwistSerreDuality (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
    (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) ⟶
      twistingSheaf R ι (-(Fintype.card ι : ℤ))) ≃ₗ[R]
      Module.Dual R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))) n) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
  letI := projectiveTopSerreMap_residueTwist_isPerfPair R ι n e m
  exact (projectiveTopSerreMap R ι n e
    (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))).toPerfPair

/-- The duality equivalence retains trace after the original actual coefficient cohomology map. -/
theorem residueTwistSerreDuality_apply (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ)
    (f : twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) ⟶
      twistingSheaf R ι (-(Fintype.card ι : ℤ)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))) n) :
    residueTwistSerreDuality R ι n e m f x =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map f) n x) :=
  projectiveTopSerreMap_apply R ι n e _ f x

end AlgebraicGeometry.Scheme.Cohomology
