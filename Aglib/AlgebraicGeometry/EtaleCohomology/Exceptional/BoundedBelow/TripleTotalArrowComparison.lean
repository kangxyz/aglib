/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCongruence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.IdentityAmbientComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionArrowTotal

/-! # The original factored total refinement gives exactly the proper associativity transport -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wW wT
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  (T : Hom.TripleCompactifiedComposition f g h) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T.first.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.leftOuter.composite.Xbar Λ`. -/
local instance tripleTotalArrowLeftModel :
    HasDerivedCategory.{wT} (ModuleSheaf T.leftOuter.composite.Xbar Λ) := hT
/-- The local derived-category model on `ModuleSheaf T.rightTotalArrowTransport.Xbar Λ`. -/
local instance tripleTotalArrowRightModel :
    HasDerivedCategory.{wT} (ModuleSheaf T.rightTotalArrowTransport.Xbar Λ) := hT

/-- The total map is the original composite refinement, normalized at its actual identity hom. -/
theorem moduleTripleTotalArrowImageComparison :
    CategoryTheory.imageComparison
        (moduleDerivedRefinementComparison T.totalArrowRefinement Λ)
        (moduleDerivedRefinementDirectImageIso Λ T.totalArrowRefinement) =
      Functor.whiskerLeft (moduleDerivedLowerShriek T.first.j Λ)
        (eqToHom (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
          (Category.assoc T.first.p T.middle.p T.last.p).symm)) := by
  have sq : IsPullback T.first.j (𝟙 X) (𝟙 T.first.Xbar) T.first.j :=
    Hom.DenseCompactification.isPullback_open (𝟙 T.leftOuter.composite)
  have ht := moduleRawImageComparison_congr Λ T.first.j T.first.j
    ((T.first.p ≫ T.middle.p) ≫ T.last.p) (T.first.p ≫ T.middle.p ≫ T.last.p)
    T.totalArrowRefinement.hom (𝟙 T.first.Xbar) T.totalArrowRefinement_hom
    (Hom.DenseCompactification.isPullback_open T.totalArrowRefinement) sq
    T.totalArrowRefinement.base_fac
    ((Category.id_comp _).trans (Category.assoc T.first.p T.middle.p T.last.p).symm)
  exact ht.trans (moduleRawImageComparison_identity_eq T.first.j sq Λ _ _
    (Category.assoc T.first.p T.middle.p T.last.p).symm)

/-- This is the literal original mixed transition on torsion inputs. -/
theorem moduleTripleTotalArrowMixedComparison :
    @moduleCompactificationMixedTransition X W ((f ≫ g) ≫ h) _ Λ _ hX hW
        T.leftOuter.composite T.rightTotalArrowTransport T.totalArrowRefinement hT hT =
      Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
        (Functor.whiskerLeft (moduleDerivedLowerShriek T.first.j Λ)
          (eqToHom (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
            (Category.assoc T.first.p T.middle.p T.last.p).symm))) :=
  congrArg (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι)
    (moduleTripleTotalArrowImageComparison T Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
