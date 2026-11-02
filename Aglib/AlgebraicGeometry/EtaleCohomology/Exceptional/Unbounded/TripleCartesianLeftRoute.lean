/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleCartesianMaps
public import Aglib.CategoryTheory.Functor.ImageLeftRoute

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
local instance unboundedTripleCartesianLeftLocal1 : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

local instance unboundedTripleCartesianLeftLocal2 : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance unboundedTripleCartesianLeftLocal3 : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

omit middleModel in
/-- The left Cartesian route is literally the original binary-map route of the raw theorem. -/
theorem moduleUnboundedTripleCartesianLeftRoute :
    Functor.whiskerRight (moduleUnboundedTripleLeftInnerMap T Λ)
        (moduleUnboundedDerivedLowerShriek T.last.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ
          T.last.p) ≫
      moduleUnboundedTripleLeftOuterMap T Λ =
    imageLeftRoute
      (moduleUnboundedProperOpenMate T.leftInner.first.p T.leftInner.middleOpen T.tail.first.j
        T.leftInner.sourceCompactification.p T.leftInner.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate (T.leftInner.sourceCompactification.p ≫ T.tail.first.p)
        T.innerToFirst T.last.j (T.first.p ≫ T.middle.p) (T.isPullback_innerToFirst.paste_horiz
        T.tail.isPullback_middleOpen.flip) Λ)
      (moduleUnboundedDerivedDirectImageCompIso Λ T.tail.first.p
        T.leftInner.sourceCompactification.p)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j T.leftInner.middleOpen
        T.leftInner.sourceCompactification.j T.leftInner.first_j_middleOpen)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.sourceCompactification.j
        T.innerToFirst
        T.first.j T.leftInner_j_innerToFirst)
      (moduleUnboundedDerivedDirectImageCompIso Λ T.last.p (T.first.p ≫ T.middle.p)).symm := by
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
