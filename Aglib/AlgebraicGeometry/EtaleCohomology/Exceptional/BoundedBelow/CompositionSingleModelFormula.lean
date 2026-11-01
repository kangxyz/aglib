/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRawSquare

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
bounded-below torsion functors. Their actual refinement cube and an actual common
refinement prove independence of the supplied compactification tower. This file
addresses binary composition; associativity and unit coherence are separate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG wRaw wTop

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))
  (hTop : HasDerivedCategory.{wTop} (ModuleSheaf C.composite.Xbar Λ))

variable (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)
  (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)

include sqMid in
/-- The native transported iso has exactly the original Cartesian map as its underlying hom. -/
theorem moduleExceptionalCompositionSingleModelIso_hom_app :
    ((moduleExceptionalCompositionSingleModelIso f g Λ C F hRaw hTop).hom.app K).hom =
      (moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hRaw
        (secondModels C.targetCompactification) hTop).app K := by
  let source := compositionPairIso
    (moduleExceptionalSingleTorsionValueIso f Λ F hRaw)
    (moduleExceptionalSingleTorsionValueIso g Λ C.targetCompactification
      (secondModels C.targetCompactification))
  let sourceAmbient := (moduleTorsionCohomologyPlus Z Λ).ι.mapIso (source.app K)
  have hc := congrArg (fun e => (e.hom.app K).hom)
    (moduleExceptionalCompositionSingleModelIso_comparison f g Λ C F hRaw hTop)
  simp only [Iso.trans_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom] at hc
  have hr := moduleExceptionalCompositionRawSquare f g Λ C F hRaw hTop m sq a sqMid hj K
  exact (cancel_epi sourceAmbient.hom).1 (hc.trans hr.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
