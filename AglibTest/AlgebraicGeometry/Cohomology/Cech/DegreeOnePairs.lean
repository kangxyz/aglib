/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeOnePairs

/-! Focused consumer of degree-one Čech homology of the structure sheaf as pair cohomology:
cycles are pair cocycles, boundaries are pair coboundaries, and the comparison with
`(structureCechComplex X U).homology 1` respects the structural scalars. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

variable {F : Type u} [Field F] (X : FScheme F) {ι : Type u} (U : ι → X.left.Opens)

example : PairCohomology U ≃+ (structureCechComplex X U).homology 1 :=
  pairCohomologyEquivCech X U

example (x : (structureCechComplex X U).X 1) :
    (structureCechComplex X U).d 1 2 x = 0 ↔ cechToPairs x ∈ pairCocycles U :=
  cech_d_one_eq_zero_iff x

example (y : (structureCechComplex X U).X 0) :
    cechToPairs ((structureCechComplex X U).d 0 1 y) = pairCoboundary U (cechToSingles y) :=
  cechToPairs_d_zero y

example (a : F) (b : pairCocycles U) :
    pairCohomologyEquivCech X U
        (QuotientAddGroup.mk ⟨pairSMul X U a b.1, pairSMul_mem X U a b.2⟩) =
      a • pairCohomologyEquivCech X U (QuotientAddGroup.mk b) :=
  pairCohomologyEquivCech_smul X U a b

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.pairCohomologyEquivCech' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pairCohomologyEquivCech

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.pairCohomologyEquivCech_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pairCohomologyEquivCech_smul
