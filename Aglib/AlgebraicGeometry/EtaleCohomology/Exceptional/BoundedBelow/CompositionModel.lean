/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Comparison
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-! # Composition through a supplied actual compactification tower

The comparison is the original proper/open comparison, followed by the original
open and proper compositors. The three middle model families are independent;
the source ambient scheme uses exactly the composite compactification's model.
This is a supplied-tower natural isomorphism. Independence of the tower requires
the additional refinement cube, and is not claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  (C : Hom.CompactifiedComposition f g)

/-- The original tower comparison with the target torsion property forgotten. -/
def moduleCompactifiedCompositionAmbientIso :
    (moduleCompactificationTorsionFunctor f Λ C.first ⋙
        moduleCompactificationTorsionFunctor g Λ C.targetCompactification) ⋙
          (moduleTorsionCohomologyPlus Z Λ).ι ≅
      moduleCompactificationFunctor (f ≫ g) Λ C.composite := by
  let : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
    compositeModels C.composite
  let L : (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleTorsionCohomologyPlus C.first.Xbar Λ).FullSubcategory :=
    (moduleTorsionCohomologyPlus C.first.Xbar Λ).lift
      ((moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek C.first.j Λ)
      (fun K => moduleDerivedLowerShriek_preservesTorsionCohomology C.first.j Λ K.property)
  let e := moduleProperOpenComparisonIso Λ C.sourceCompactification.p C.first.p
    C.targetCompactification.j C.middleOpen C.isPullback_middleOpen
  let c : moduleDerivedLowerShriek C.first.j Λ ⋙ moduleDerivedLowerShriek C.middleOpen Λ ≅
      moduleDerivedLowerShriek C.sourceCompactification.j Λ :=
    (moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
      eqToIso (moduleDerivedLowerShriek_congr Λ C.first_j_middleOpen)
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft L e)
      (moduleDerivedDirectImage Λ C.targetCompactification.p) ≪≫
    Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (Functor.isoWhiskerRight c
        (moduleDerivedDirectImage Λ C.sourceCompactification.p ⋙
          moduleDerivedDirectImage Λ C.targetCompactification.p)) ≪≫
    Functor.isoWhiskerLeft
      ((moduleTorsionCohomologyPlus X Λ).ι ⋙
        moduleDerivedLowerShriek C.sourceCompactification.j Λ)
      (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm

/-- The supplied-tower comparison in the native torsion full subcategory. -/
def moduleCompactifiedCompositionIso :
    moduleCompactificationTorsionFunctor f Λ C.first ⋙
        moduleCompactificationTorsionFunctor g Λ C.targetCompactification ≅
      moduleCompactificationTorsionFunctor (f ≫ g) Λ C.composite :=
  NatIso.ofComponents
    (fun K => (moduleTorsionCohomologyPlus Z Λ).isoMk
      ((moduleCompactifiedCompositionAmbientIso f g Λ C).app K)) (by
        intro K K' a
        apply ObjectProperty.hom_ext
        exact (moduleCompactifiedCompositionAmbientIso f g Λ C).hom.naturality a)

omit [QuasiCompact f] in
/-- The torsion lift retains the exact original ambient comparison component. -/
theorem moduleCompactifiedCompositionIso_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactifiedCompositionIso f g Λ C).hom.app K).hom =
      (moduleCompactifiedCompositionAmbientIso f g Λ C).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
