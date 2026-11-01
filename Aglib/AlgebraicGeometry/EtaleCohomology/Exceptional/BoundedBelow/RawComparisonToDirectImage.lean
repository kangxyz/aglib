/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RawToDirectImage
public import Aglib.CategoryTheory.NatTrans.TargetComparisonTransport

/-! # The same chosen canonical map is computed through every original raw compactification -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wM
variable {X S : Scheme.{u}} {f : X ⟶ S}
  [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (C : Hom.Compactification f) [QuasiCompact C.j]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [middleModels : ∀ D : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ)]

/-- The chosen comparison to a raw model uses its original densification inverse. -/
def moduleExceptionalRawComparisonIso :
    moduleExceptionalDirectImagePlus f Λ ≅ moduleRawCompactificationFunctor C Λ :=
  moduleExceptionalDirectImagePlusIso f Λ (Hom.Compactification.densify C) ≪≫
    (@moduleCompactificationDensificationIso X S f C _ Λ _ hX hS hC
      (middleModels (Hom.Compactification.densify C))).symm

/-- Densification and canonical choice descent preserve the same original map. -/
theorem moduleExceptionalToDirectImage_raw_model :
    TargetComparisonEquation (moduleExceptionalRawComparisonIso C Λ).hom
      (moduleRawCompactificationToDirectImage C Λ) (moduleExceptionalToDirectImage f Λ) :=
  targetComparison_iso_inv
    (moduleExceptionalDirectImagePlusIso f Λ (Hom.Compactification.densify C))
    (@moduleCompactificationDensificationIso X S f C _ Λ _ hX hS hC
      (middleModels (Hom.Compactification.densify C)))
    (moduleExceptionalToDirectImage f Λ) (moduleRawCompactificationToDirectImage C Λ)
    (moduleRawCompactificationToDirectImage (Hom.Compactification.densify C).toCompactification Λ)
    (moduleExceptionalToDirectImage_model f Λ (Hom.Compactification.densify C))
    (moduleRawCompactificationToDirectImage_densification C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
