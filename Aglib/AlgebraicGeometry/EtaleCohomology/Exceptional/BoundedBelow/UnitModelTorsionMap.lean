/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion

/-! # The native single-value lift retains literal original objects and maps -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC
variable {X S : Scheme.{u}} {f : X ⟶ S} (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  (C : Hom.DenseCompactification f)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))

/-- Forgetting the native property does not alter the original value. -/
theorem moduleCompactificationSingleTorsionValue_obj
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactificationSingleTorsionValue Λ C hC).obj K).obj =
      (@moduleDerivedDirectImage S Λ _ C.Xbar C.p hS hC).obj
        ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hC).obj K.obj) := rfl

/-- Forgetting the native property does not alter the original map. -/
theorem moduleCompactificationSingleTorsionValue_map_hom
    {K L : (moduleTorsionCohomologyPlus X Λ).FullSubcategory} (a : K ⟶ L) :
    ((moduleCompactificationSingleTorsionValue Λ C hC).map a).hom =
      (@moduleDerivedDirectImage S Λ _ C.Xbar C.p hS hC).map
        ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hC).map a.hom) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
