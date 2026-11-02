/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceMultiplicative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Artinian

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

universe u w₁

variable {X : Scheme.{u}} (U : X.Etale) [IsArtinianScheme U.left]

attribute [local instance] hasSheafifyLarge

variable [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual degree-one Ext from the overlap representable to the original Gm
sheaf vanishes for an Artinian etale overlap. -/
theorem subsingleton_ext_one_gm_of_isArtinianScheme :
    Subsingleton (Ext.{w₁}
      (freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X)
        U) (gm X) 1) := by
  let : HasExt.{u + 2} (Sheaf ((Scheme.smallEtaleTopology X).over U)
      AddCommGrpCat.{u + 1}) := HasExt.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} U.left) := hasExtStandard U.left
  let : Subsingleton (Sheaf.H.{u + 2} (gm U.left) 1) :=
    Picard.gmH1_subsingleton_of_isArtinianScheme.{u, u + 2} U.left
  exact (Kummer.gmRepresentedCohomologyEquiv.{u, w₁, u + 2, u + 2} U 1).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
