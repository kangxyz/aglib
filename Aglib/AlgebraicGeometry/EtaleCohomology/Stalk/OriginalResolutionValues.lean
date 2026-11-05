/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheaf

/-! # Original values of the original resolution comparison -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

local instance originalResolutionValues_small
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (U : S.Etale) :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
  originalCohomologyPresheaf_small f F q (op U)

/-- Evaluate the existing resolution comparison before composing any other comparison. -/
theorem smallOriginalCohomologyResolutionIso_apply_shrink
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (U : S.Etale)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    (smallOriginalCohomologyResolutionIso f F q).hom.app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm x) =
      originalCohomologyResolutionEquiv f U F q x :=
  congrArg (originalCohomologyResolutionEquiv f U F q)
    (Shrink.addEquiv.{u + 1, w}.apply_symm_apply x)

end AlgebraicGeometry.Scheme.EtaleCohomology
