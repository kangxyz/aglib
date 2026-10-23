/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SliceComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Artinian
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Comparison

/-! # Original represented-object multiplicative H1 of Artinian overlaps

The original free-representable Ext group is compared with original slice
cohomology, then with the actual small-etale cohomology of the overlap. Native
Artinian Picard triviality gives the vanishing. This is the degree-one input
needed by the actual two-kernel degree-two Cech criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w₁ w₂ w₃

variable {X : Scheme.{u}} (U : X.Etale) [IsArtinianScheme U.left]

attribute [local instance] hasSheafifyLarge

variable [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over
    U) AddCommGrpCat.{u + 1})]
  [HasExt.{w₃} (AbelianSheaf.{u, u + 1} U.left)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual degree-one Ext from the overlap representable to the original Gm
sheaf vanishes for an Artinian etale overlap. -/
theorem subsingleton_ext_one_gm_of_isArtinianScheme :
    Subsingleton (Ext.{w₁}
      (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X)
        U) (gm X) 1) := by
  let J := Scheme.smallEtaleTopology X
  let e₁ := Sheaf.SliceCohomology.sliceComparison.{w₁, w₂, u + 1, u, u + 1}
    J U (gm X) 1
  let e₂ := sliceCohomologyEquiv.{u, u + 1, w₂, w₃} U (gm U.left) 1
  let e₃ := ((Sheaf.functorH.{w₂, u + 1, u, u + 1} (J.over U) 1).mapIso
    (gmEtaleSliceIso U)).addCommGroupIsoToAddEquiv
  refine ⟨fun a b => e₁.injective (e₃.toEquiv.symm.injective
    (e₂.toEquiv.symm.injective ?_))⟩
  exact (Picard.gmH1_subsingleton_of_isArtinianScheme.{u, w₃} U.left).elim _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
