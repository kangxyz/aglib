/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Large
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Naturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Ordinary
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic

/-!
# Slice cohomology on the original small-etale site

This entry discharges the site and coefficient sizes used by the existing
etale cohomology API: scheme universe `u`, abelian values `u+1`, Ext `u+2`.
No geometric proper-base-change result is used or asserted here.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (U : X.Etale)

local instance : HasSheafify ((Scheme.smallEtaleTopology X).over U)
    AddCommGrpCat.{u + 1} := by infer_instance

local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
local instance : HasExt.{u + 2}
    (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- Original small-etale slice comparison at the actual large coefficient sizes. -/
def etaleSliceComparison (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F n U ≃+
      Sheaf.H.{u + 2} (F.over U) n :=
  Sheaf.SliceCohomology.largeStandardSliceComparison.{u + 1, u}
    (Scheme.smallEtaleTopology X) U F n

end AlgebraicGeometry.Scheme.EtaleCohomology
