/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleCartesianMaps
public import Aglib.CategoryTheory.Functor.ImageRightRealization
public import Aglib.CategoryTheory.Functor.ImageCompositionTarget
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TripleHorizontalOpenTransport

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
local instance tripleCartesianRightLocal1 : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

local instance tripleCartesianRightLocal2 : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance tripleCartesianRightLocal3 : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

omit hA₁ in
/-- The actual right maps retain the original final transport in a whole typed equation. -/
theorem moduleTripleCartesianRightRoute :
    ImageRightRealizationEquation
      (K := moduleDerivedLowerShriek T.leftInner.first.j Λ)
      (J := moduleDerivedLowerShriek T.first.j Λ)
      (Q₀ := moduleDerivedDirectImage Λ T.leftInner.first.p)
      (I₁ := moduleDerivedLowerShriek T.tail.first.j Λ)
      (Q₁ := moduleDerivedDirectImage Λ T.tail.first.p)
      (I₂ := moduleDerivedLowerShriek T.last.j Λ)
      (M := moduleDerivedLowerShriek T.tail.middleOpen Λ)
      (R := moduleDerivedDirectImage Λ T.middle.p)
      (Hsrc := moduleDerivedLowerShriek (T.tail.first.j ≫ T.tail.middleOpen) Λ)
      (Hsrc' := moduleDerivedLowerShriek T.tail.sourceCompactification.j Λ)
      (Htgt := moduleDerivedLowerShriek (T.leftInner.middleOpen ≫ T.innerToFirst) Λ)
      (R₀₂ := moduleDerivedDirectImage Λ T.first.p)
      (P := moduleDerivedDirectImage Λ T.last.p)
      (Stail := moduleDerivedDirectImage Λ (T.middle.p ≫ T.last.p))
      (S := moduleDerivedDirectImage Λ (T.first.p ≫ T.middle.p ≫ T.last.p))
      (S' := moduleDerivedDirectImage Λ ((T.first.p ≫ T.middle.p) ≫ T.last.p))
      (moduleProperOpenMate Λ T.last.j T.tail.middleOpen T.tail.first.p T.middle.p
        T.tail.isPullback_middleOpen.flip)
      (moduleProperOpenMate Λ (T.tail.first.j ≫ T.tail.middleOpen)
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p T.first.p
        (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst))
      (moduleDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j)
      (moduleDerivedLowerShriekOverIso Λ T.leftInner.first.j
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (tripleFirstOpenEquality T))
      (moduleDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
      (moduleDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm
      (eqToIso (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
        (Category.assoc T.first.p T.middle.p T.last.p).symm))
      (moduleTripleTailMap T Λ) (moduleTripleRightOuterMap T Λ) := by
  let σb := moduleProperOpenMate Λ T.last.j T.tail.middleOpen T.tail.first.p T.middle.p
    T.tail.isPullback_middleOpen.flip
  let σh := moduleProperOpenMate Λ (T.tail.first.j ≫ T.tail.middleOpen)
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p T.first.p
    (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst)
  let σh' := moduleProperOpenMate Λ T.tail.sourceCompactification.j
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p T.first.p
    T.isPullback_first.flip
  let dh := moduleDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j
  let e := eqToIso (moduleDerivedLowerShriek_congr Λ T.tail.first_j_middleOpen)
  let c := moduleDerivedLowerShriekOverIso Λ T.leftInner.first.j
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (tripleFirstOpenEquality T)
  let sTail := (moduleDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
  let s := (moduleDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm
  let ep := eqToIso (congrArg (fun p : T.first.Xbar ⟶ W => moduleDerivedDirectImage Λ p)
    (Category.assoc T.first.p T.middle.p T.last.p).symm)
  exact imageRightRealizationEquation σb σh σh' dh e
    (moduleTripleHorizontalOpenTransport T Λ) c sTail s ep
    (moduleTripleTailMap T Λ) (moduleTripleRightOuterMap T Λ) rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
