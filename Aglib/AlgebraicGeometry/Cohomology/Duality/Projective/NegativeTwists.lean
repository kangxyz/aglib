/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.NegativeTop
public import Aglib.AlgebraicGeometry.Cohomology.Duality.LaurentPairing.Pieces

/-!
# Original negative-twist top cohomology and its native Laurent piece

The actual cohomology of a negative twist is identified with the existing supported
all-negative Laurent submodule. The map uses the original Laurent/Cech comparison and
weight traces, and its original-cycle formula retains every Laurent coefficient.
All projective dimensions, including zero, and arbitrary commutative rings are allowed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The original top cohomology of a negative twist is the existing native supported
all-negative Laurent piece, linearly over the original structural base ring. -/
def twistingNegativeTopCohomologyLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : d < 0) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) n ≃ₗ[R]
      coordinateNegativePiece (ι := ι) R d := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
  exact (twistingLaurentCohomologyLinearEquiv R ι d n).symm.trans
    ((coordinateLaurentTupleNegativeTopWeightsEquiv R n e d hd).trans
      (coordinateNegativePieceEquivFinsupp R d).symm)

/-- Every original coefficient of the native negative piece is the original weight trace
of the same actual cohomology class under the unchanged Laurent comparison. -/
theorem twistingNegativeTopCohomologyLinearEquiv_coeff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : d < 0)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) n)
    (w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ}) :
    (twistingNegativeTopCohomologyLinearEquiv R ι n e d hd x).val.coeff
        (coordinateFullWeightEquiv d w).val =
      coordinateLaurentWeightTrace R n e d w.val w.property
        ((twistingLaurentCohomologyLinearEquiv R ι d n).symm x) := by
  rw [← coordinateNegativePieceEquivFinsupp_apply]
  change coordinateNegativePieceEquivFinsupp R d
    ((coordinateNegativePieceEquivFinsupp R d).symm
      (coordinateLaurentTupleNegativeTopWeightsEquiv R n e d hd
        ((twistingLaurentCohomologyLinearEquiv R ι d n).symm x)))
      (coordinateFullWeightEquiv d w) = _
  rw [LinearEquiv.apply_symm_apply]
  exact coordinateLaurentTupleNegativeTopWeightsEquiv_apply R n e d hd _ w

/-- On the original Laurent cycle class, the actual cohomology comparison retains the
literal original Laurent coefficient on the enumerated coordinate tuple. -/
theorem twistingNegativeTopCohomologyLinearEquiv_laurent_homologyπ_coeff
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : d < 0)
    (c : (coordinateLaurentTupleComplex (ι := ι) R d).cycles n)
    (w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ}) :
    (twistingNegativeTopCohomologyLinearEquiv R ι n e d hd
        (twistingLaurentCohomologyLinearEquiv R ι d n
          ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c))).val.coeff
        (coordinateFullWeightEquiv d w).val =
      ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c e.symm).val.coeff
        (coordinateWeightExponent e.symm w.val (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) := by
  rw [twistingNegativeTopCohomologyLinearEquiv_coeff, LinearEquiv.symm_apply_apply]
  exact coordinateLaurentWeightTrace_homologyπ R n e d w.val w.property c

end AlgebraicGeometry.Scheme.Cohomology
