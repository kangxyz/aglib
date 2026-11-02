/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleCartesianLeftRoute
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleCartesianRightRoute
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleRawComposition
public import Aglib.CategoryTheory.Functor.ImageCartesianComposition

/-! # Actual triple-tower interchange associativity

All three Cartesian squares are the literal open restrictions of the supplied
three-level tower. No geometric compatibility or map coherence is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wW wA₀ wA₁ wA₂ wB₀ wB₁ wY wZ wC
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact g] [QuasiCompact h] (T : Hom.TripleCompactifiedComposition f g h)
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hW : HasDerivedCategory.{wW} (ModuleSheaf W Λ)]
  [hA₀ : HasDerivedCategory.{wA₀} (ModuleSheaf T.leftInner.first.Xbar Λ)]
  [hA₁ : HasDerivedCategory.{wA₁} (ModuleSheaf T.leftInner.sourceCompactification.Xbar Λ)]
  [hA₂ : HasDerivedCategory.{wA₂} (ModuleSheaf T.first.Xbar Λ)]
  [hB₀ : HasDerivedCategory.{wB₀} (ModuleSheaf T.tail.first.Xbar Λ)]
  [middleModel : HasDerivedCategory.{wB₁} (ModuleSheaf T.middle.Xbar Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf T.last.Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf T.tail.sourceCompactification.Xbar Λ`. -/
local instance tripleCartesianCompositionLocal1 : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

local instance tripleCartesianCompositionLocal2 : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance tripleCartesianCompositionLocal3 : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

/-- The actual four Cartesian maps retain the original final proper transport. -/
theorem moduleTripleCartesianComposition :
    ImageCartesianCompositionEquation
      (K := moduleDerivedLowerShriek T.leftInner.first.j Λ)
      (J₁ := moduleDerivedLowerShriek T.leftInner.sourceCompactification.j Λ)
      (J₂ := moduleDerivedLowerShriek T.first.j Λ)
      (Q₀ := moduleDerivedDirectImage Λ T.leftInner.first.p)
      (I₁ := moduleDerivedLowerShriek T.tail.first.j Λ)
      (Q₁ := moduleDerivedDirectImage Λ T.tail.first.p)
      (I₂ := moduleDerivedLowerShriek T.last.j Λ)
      (Vsrc := moduleDerivedDirectImage Λ
        (T.leftInner.sourceCompactification.p ≫ T.tail.first.p))
      (P := moduleDerivedDirectImage Λ T.last.p)
      (Hsrc' := moduleDerivedLowerShriek T.tail.sourceCompactification.j Λ)
      (Stail := moduleDerivedDirectImage Λ (T.middle.p ≫ T.last.p))
      (Sright := moduleDerivedDirectImage Λ (T.first.p ≫ T.middle.p ≫ T.last.p))
      (S := moduleDerivedDirectImage Λ ((T.first.p ≫ T.middle.p) ≫ T.last.p))
      (eqToIso (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
        (Category.assoc T.first.p T.middle.p T.last.p).symm))
      (moduleTripleLeftInnerMap T Λ) (moduleTripleLeftOuterMap T Λ)
      (moduleTripleTailMap T Λ) (moduleTripleRightOuterMap T Λ) := by
  exact imageCartesianCompositionEquation
      (moduleProperOpenMate Λ T.tail.first.j T.leftInner.middleOpen
        T.leftInner.first.p T.leftInner.sourceCompactification.p
        T.leftInner.isPullback_middleOpen.flip)
      (moduleProperOpenMate Λ T.last.j T.tail.middleOpen T.tail.first.p T.middle.p
        T.tail.isPullback_middleOpen.flip)
      (moduleProperOpenMate Λ T.last.j T.innerToFirst
        (T.leftInner.sourceCompactification.p ≫ T.tail.first.p) (T.first.p ≫ T.middle.p)
        (T.isPullback_innerToFirst.paste_horiz T.tail.isPullback_middleOpen.flip))
      (moduleProperOpenMate Λ (T.tail.first.j ≫ T.tail.middleOpen)
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p T.first.p
        (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst))
      (moduleDerivedDirectImageCompIso Λ T.tail.first.p T.leftInner.sourceCompactification.p)
      (moduleDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j)
      (moduleDerivedLowerShriekOverIso Λ T.leftInner.first.j T.leftInner.middleOpen
        T.leftInner.sourceCompactification.j T.leftInner.first_j_middleOpen)
      (moduleDerivedLowerShriekOverIso Λ T.leftInner.sourceCompactification.j T.innerToFirst
        T.first.j T.leftInner_j_innerToFirst)
      (moduleDerivedLowerShriekOverIso Λ T.leftInner.first.j
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (tripleFirstOpenEquality T))
      (moduleDerivedDirectImageCompIso Λ T.last.p (T.first.p ≫ T.middle.p)).symm
      (moduleDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
      (moduleDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm
      (eqToIso (congrArg (fun q : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ q)
        (Category.assoc T.first.p T.middle.p T.last.p).symm))
    (moduleTripleLeftInnerMap T Λ) (moduleTripleLeftOuterMap T Λ)
    (moduleTripleTailMap T Λ) (moduleTripleRightOuterMap T Λ)
    (moduleTripleRawCompositionEquation T Λ)
    (moduleTripleCartesianLeftRoute T Λ) (moduleTripleCartesianRightRoute T Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
