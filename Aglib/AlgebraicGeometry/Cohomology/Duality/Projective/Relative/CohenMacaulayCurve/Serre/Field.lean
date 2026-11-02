/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Field
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Serre.Derived

/-!
# Original curve cohomology and field constants

This specializes the original constants-action comparison to the structural map of
the chosen projective curve. No Cohen--Macaulay or projectivity hypothesis is needed
for the comparison itself, and no canonical object or trace is changed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The coefficient Serre carrier and FScheme carrier retain the same original action. -/
def cmCurveSerreCohomologyFieldLinearEquiv
    (k : Type u) [Field k] (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) (M : C.Modules) (q : ℕ) :
    cmCurveSerreCohomology k ι j M q ≃ₗ[k]
      moduleCohomology k (Over.mk (j ≫ toSpec k ι)) M q :=
  (moduleCohomologyConstantsIso (Over.mk (j ≫ toSpec k ι)) M q).toLinearEquiv

theorem cmCurveSerreCohomologyField_finrank
    (k : Type u) [Field k] (ι : Type u) {C : Scheme.{u}}
    (j : C ⟶ ProjectiveSpace k ι) (M : C.Modules) (q : ℕ) :
    Module.finrank k (cmCurveSerreCohomology k ι j M q) =
      Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι)) M q) :=
  (cmCurveSerreCohomologyFieldLinearEquiv k ι j M q).finrank_eq

end AlgebraicGeometry.Scheme.Cohomology
