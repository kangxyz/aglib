/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.SliceComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison

/-! # Original represented multiplicative cohomology on etale charts

The comparison uses the actual multiplicative coefficient on the small-etale
slice. It does not assert multiplicative-coefficient invariance under arbitrary
scheme inverse image. The three original Ext universes remain independent.
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

/-- Original represented multiplicative cohomology equals original chart cohomology. -/
def gmRepresentedCohomologyEquiv (q : ℕ) :
    Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
        X.smallEtaleTopology (gm X) q U ≃+
      Sheaf.H.{w''} (gm U.left) q := by
  let e₁ := Sheaf.SliceCohomology.sliceComparison.{w, w', u + 1, u, u + 1}
    X.smallEtaleTopology U (gm X) q
  let e₂ := ((Sheaf.functorH.{w', u + 1, u, u + 1}
    (X.smallEtaleTopology.over U) q).mapIso (gmEtaleSliceIso U))
  let e₃ := sliceCohomologyEquiv.{u, u + 1, w', w''} U (gm U.left) q
  exact e₁.trans (e₂.addCommGroupIsoToAddEquiv.symm.trans e₃.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
