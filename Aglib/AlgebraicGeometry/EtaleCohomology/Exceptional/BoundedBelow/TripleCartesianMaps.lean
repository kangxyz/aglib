/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianUnderlyingMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleOpenContraction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImageContraction
public import Aglib.CategoryTheory.Functor.ImageTripleCompositionPredicate
public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionSquares

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
local instance tripleCartesianMapsLocal1 : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

local instance tripleCartesianMapsLocal2 : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance tripleCartesianMapsLocal3 : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

/-- The first binary map is the existing original Cartesian map on its full ambient source. -/
def moduleTripleLeftInnerMap :=
  moduleCartesianCompositionUnderlyingMap T.leftInner T.leftInner.first T.leftInner.middleOpen
    T.leftInner.isPullback_middleOpen T.leftInner.first_j_middleOpen
    Λ hX hY hZ hA₀ hB₀ hA₁

/-- The left outer map uses the literal intermediate open restriction. -/
def moduleTripleLeftOuterMap :=
  moduleCartesianCompositionUnderlyingMap T.leftOuter T.leftInner.composite T.innerToFirst
    T.isPullback_leftInner T.leftInner_j_innerToFirst Λ hX hZ hW hA₁ hC hA₂

/-- The tail binary map retains its actual middle open, not the factored replacement. -/
def moduleTripleTailMap :=
  moduleCartesianCompositionUnderlyingMap T.tail T.tail.first T.tail.middleOpen
    T.tail.isPullback_middleOpen T.tail.first_j_middleOpen Λ hY hZ hW hB₀ hC middleModel

/-- The right outer map uses the literal composed source restriction and actual middle open. -/
def moduleTripleRightOuterMap :=
  moduleCartesianCompositionUnderlyingMap T.rightOuter T.leftInner.first
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.isPullback_first
    (tripleFirstOpenEquality T) Λ hX hY hW hA₀ middleModel hA₂

end AlgebraicGeometry.Scheme.EtaleCohomology
