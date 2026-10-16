/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.ResidueTrace

/-!
# The original geometric projective residue trace

The original Laurent/Cech comparison identifies unchanged actual cohomology of
`O(-card ι)` with native residue-degree homology. Composing with the existing literal
coefficient trace gives the geometric trace isomorphism. Its cycles formula retains the
original all-minus-one coefficient on the chosen enumeration, with positive sign.
The construction works over every commutative ring and in every dimension.
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

/-- The residue twist has the usual degree `-n-1` for the displayed projective dimension. -/
theorem projectiveResidueDegree_eq (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    -(Fintype.card ι : ℤ) = -(n : ℤ) - 1 := by
  rw [Fintype.card_congr e, Fintype.card_fin]
  omega

/-- The actual top cohomology of the residue twist is the original scalar ring, through
the original geometric Laurent comparison and unchanged coefficient residue trace. -/
def projectiveTraceLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ)))) n ≃ₗ[R] R := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
  exact (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n).symm.trans
    (coordinateLaurentResidueTraceEquiv R n e)

/-- The original actual-cohomology trace, as its native structural-ring linear map. -/
abbrev projectiveTrace (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(Fintype.card ι : ℤ)))) n →ₗ[R] R := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
    (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n
  exact (projectiveTraceLinearEquiv R ι n e).toLinearMap

/-- Original Laurent cohomology classes retain exactly their original coefficient trace
under the actual geometric comparison. -/
theorem projectiveTrace_laurent (n : ℕ) (e : ι ≃ Fin (n + 1))
    (x : (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homology n) :
    projectiveTrace R ι n e
        (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n x) =
      coordinateLaurentWeightTrace R n e (-(Fintype.card ι : ℤ))
        coordinateResidueWeight coordinateResidueWeight_fullSupport x := by
  change coordinateLaurentResidueTraceEquiv R n e
    ((twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n).symm
      (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n x)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The actual geometric trace of an original Laurent cycle class is the literal original
all-minus-one coefficient on the enumerated tuple, with no sign or scalar correction. -/
theorem projectiveTrace_laurent_homologyπ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (c : (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).cycles n) :
    projectiveTrace R ι n e
        (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n
          ((coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homologyπ n c)) =
      ((coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).iCycles n c
        e.symm).val.coeff (coordinateWeightExponent e.symm coordinateResidueWeight
          (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) := by
  rw [projectiveTrace_laurent]
  exact coordinateLaurentWeightTrace_homologyπ R n e _ coordinateResidueWeight
    coordinateResidueWeight_fullSupport c

end AlgebraicGeometry.Scheme.Cohomology
