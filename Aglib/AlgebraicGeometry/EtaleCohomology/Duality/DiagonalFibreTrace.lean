/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! Trace of the original diagonal on the original section fibre. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

open Coefficients Scheme.OverField Scheme.OverField.Curve Scheme.OverField.Curve.PointDivisor
open Scheme.Modules.Invertible GroupCohomology.Kummer.CoefficientBaseChange

universe u wX wZ wAX wAZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (o : Base k ⟶ Y.left) (ho : o ≫ Y.hom = 𝟙 (Base k))
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  (hi : IsUnit (n : Γ(pullback Y.hom Y.hom, ⊤)))
  [HasExt.{wX} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} Y.left)]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback Y.hom Y.hom))]

/-- The original diagonal evaluated on the original section fibre has trace one. -/
theorem traceAddEquiv_diagonalModuleKummerClass_pullback_sectionFibre :
    letI : SmoothOfRelativeDimension 1 Y.hom := hY.smooth
    letI : IsProper Y.hom := hY.proper
    let j := diagonalSectionFibreMap Y.hom o ho
    traceAddEquiv hY n hn hunit (levelInvertible j n hi)
      (moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} Y.left n 2
        (moduleRootsUnitExtPullback.{u, wZ, wX} j n hn hi 2
          (Kummer.diagonalModuleKummerClass Y.hom n hn hi))) = 1 := by
  dsimp only
  let : SmoothOfRelativeDimension 1 Y.hom := hY.smooth
  let : IsProper Y.hom := hY.proper
  let j := diagonalSectionFibreMap Y.hom o ho
  rw [Kummer.diagonalModuleKummerClass_pullback_sectionFibre Y.hom o ho n hn hi,
    AddEquiv.apply_symm_apply]
  exact traceAddEquiv_picardBoundary_positiveLineBundle hY n hn hunit
    (levelInvertible j n hi) o ho

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
