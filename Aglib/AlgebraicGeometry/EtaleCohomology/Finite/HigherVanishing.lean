/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteDirectImageExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Exact

/-! # Positive original higher direct images vanish for finite morphisms -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u wX wS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]

/-- Finite direct image is exact in the native homology interface. -/
instance finiteDirectImage_preservesHomology : (directImage f).PreservesHomology :=
  directImage_preservesHomology_of_preservesEpimorphisms f

/-- Finite direct image preserves actual finite colimits of original sheaves. -/
instance finiteDirectImage_preservesFiniteColimits : PreservesFiniteColimits (directImage f) :=
  directImage_preservesFiniteColimits_of_preservesEpimorphisms f

/-- Positive original derived direct-image objects vanish, with independent
source and target derived-category universe inputs retained. -/
theorem isZero_higherDirectImage_obj_of_isFinite
    [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj F) :=
  isZero_higherDirectImage_obj_of_preservesHomology f F q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
