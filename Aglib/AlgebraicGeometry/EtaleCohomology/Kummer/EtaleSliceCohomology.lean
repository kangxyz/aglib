/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceRoots
public import Aglib.AlgebraicGeometry.EtaleCohomology.SliceComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison

/-!
# Original represented root-cohomology on an actual etale chart

The original free-representable Ext group is compared with original root
cohomology on the chart. All three Ext universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w' w''

variable {X : Scheme.{u}} (U : X.Etale)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (Sheaf (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1})]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} U.left)]

/-- Actual represented root-cohomology equals original root-cohomology of the chart. -/
def rootsRepresentedCohomologyEquiv (n q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} X.smallEtaleTopology (mu X n) q U ≃+
      Sheaf.H.{w''} (mu U.left n) q := by
  let e₁ := Sheaf.SliceCohomology.sliceComparison.{w, w', u + 1, u, u + 1}
    X.smallEtaleTopology U (mu X n) q
  let e₂ := ((Sheaf.functorH.{w', u + 1, u, u + 1}
    (X.smallEtaleTopology.over U) q).mapIso (rootsEtaleSliceIso U n))
  let e₃ := sliceCohomologyEquiv.{u, u + 1, w', w''} U (mu U.left n) q
  exact e₁.trans (e₂.addCommGroupIsoToAddEquiv.symm.trans e₃.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
