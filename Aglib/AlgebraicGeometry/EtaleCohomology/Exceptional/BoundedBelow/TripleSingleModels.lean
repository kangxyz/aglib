/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionSingleModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionArrowTotal
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionSquares

/-! # Original single-value models of the genuine triple tower -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wW wF wG wH wFG wGH wL wR
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  [IsSeparated f] [IsSeparated g] [IsSeparated h]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace W] [QuasiSeparatedSpace W]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [gModels : ∀ C : Hom.DenseCompactification g, HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [hModels : ∀ C : Hom.DenseCompactification h, HasDerivedCategory.{wH} (ModuleSheaf C.Xbar Λ)]
  [fgModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  [ghModels : ∀ C : Hom.DenseCompactification (g ≫ h),
    HasDerivedCategory.{wGH} (ModuleSheaf C.Xbar Λ)]
  [leftModels : ∀ C : Hom.DenseCompactification ((f ≫ g) ≫ h),
    HasDerivedCategory.{wL} (ModuleSheaf C.Xbar Λ)]
  [rightModels : ∀ C : Hom.DenseCompactification (f ≫ (g ≫ h)),
    HasDerivedCategory.{wR} (ModuleSheaf C.Xbar Λ)]

/-- The first original raw single value. -/
abbrev moduleTripleSingleFirstValue :=
  moduleCompactificationSingleTorsionValue Λ T.leftInner.first (fModels T.leftInner.first)

/-- The middle original raw single value. -/
abbrev moduleTripleSingleSecondValue :=
  moduleCompactificationSingleTorsionValue Λ T.tail.first (gModels T.tail.first)

/-- The last original raw single value. -/
abbrev moduleTripleSingleThirdValue :=
  moduleCompactificationSingleTorsionValue Λ T.last (hModels T.last)

/-- The first binary native iso retains the original chosen compositor and comparisons. -/
abbrev moduleTripleSingleInnerIso :=
  moduleExceptionalCompositionSingleModelIso f g Λ
    (firstModels := fModels) (secondModels := gModels) (compositeModels := fgModels)
    T.leftInner T.leftInner.first (fModels T.leftInner.first) (fgModels T.leftInner.composite)

/-- The left outer native iso uses the actual intermediate raw value. -/
abbrev moduleTripleSingleLeftIso :=
  moduleExceptionalCompositionSingleModelIso (f ≫ g) h Λ
    (firstModels := fgModels) (secondModels := hModels) (compositeModels := leftModels)
    T.leftOuter T.leftInner.composite
    (fgModels T.leftInner.composite) (leftModels T.leftOuter.composite)

/-- The tail native iso retains the original middle and last values. -/
abbrev moduleTripleSingleTailIso :=
  moduleExceptionalCompositionSingleModelIso g h Λ
    (firstModels := gModels) (secondModels := hModels) (compositeModels := ghModels)
    T.tail T.tail.first (gModels T.tail.first) (ghModels T.tail.composite)

/-- The right outer native iso uses the same supplied top model, not a patched family. -/
abbrev moduleTripleSingleRightIso :=
  moduleExceptionalCompositionSingleModelIso f (g ≫ h) Λ
    (firstModels := fModels) (secondModels := ghModels) (compositeModels := rightModels)
    T.rightOuter T.leftInner.first
    (fModels T.leftInner.first) (leftModels T.leftOuter.composite)

/-- The total comparison is the original mixed map along the genuine factored refinement. -/
abbrev moduleTripleSingleTotalIso :=
  moduleCompactificationSingleTorsionTransition Λ T.totalArrowRefinement
    (leftModels T.leftOuter.composite) (leftModels T.leftOuter.composite)

end AlgebraicGeometry.Scheme.EtaleCohomology
