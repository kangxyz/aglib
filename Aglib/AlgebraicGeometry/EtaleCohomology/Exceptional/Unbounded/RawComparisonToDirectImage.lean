/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawToDirectImage
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The chosen comparison to a raw model uses its original densification inverse. -/
def moduleExceptionalUnboundedRawComparisonIso :
    moduleExceptionalDirectImageUnbounded f Λ ≅ moduleUnboundedRawCompactificationFunctor C Λ :=
  moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ
      (Hom.Compactification.densify C) ≪≫
    (@moduleUnboundedCompactificationDensificationIso X S f C _ Λ _ hX hS hC
      (middleModels (Hom.Compactification.densify C)) N hN hΛ).symm

/-- Densification and canonical choice descent preserve the same original map. -/
theorem moduleExceptionalToDirectImageUnbounded_raw_model :
    TargetComparisonEquation (moduleExceptionalUnboundedRawComparisonIso C Λ N hN hΛ).hom
      (moduleUnboundedRawCompactificationToDirectImage C Λ)
      (moduleExceptionalToDirectImageUnbounded f Λ) :=
  targetComparison_iso_inv
    (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ (Hom.Compactification.densify C))
    (@moduleUnboundedCompactificationDensificationIso X S f C _ Λ _ hX hS hC
      (middleModels (Hom.Compactification.densify C)) N hN hΛ)
    (moduleExceptionalToDirectImageUnbounded f Λ)
    (moduleUnboundedRawCompactificationToDirectImage C Λ)
    (moduleUnboundedRawCompactificationToDirectImage
      (Hom.Compactification.densify C).toCompactification Λ)
    (moduleExceptionalToDirectImageUnbounded_model f Λ N hN hΛ
      (Hom.Compactification.densify C))
    (moduleUnboundedRawCompactificationToDirectImage_densification C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
