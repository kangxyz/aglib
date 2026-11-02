/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleCartesianMaps
public import Aglib.CategoryTheory.Functor.ImageRightRealization
public import Aglib.CategoryTheory.Functor.ImageCompositionTarget
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.TripleHorizontalOpenTransport

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
local instance unboundedTripleCartesianRightLocal1 : HasDerivedCategory.{wB₁}
    (ModuleSheaf T.tail.sourceCompactification.Xbar Λ) := middleModel

local instance unboundedTripleCartesianRightLocal2 : IsOpenImmersion
    (show T.leftInner.composite.Xbar ⟶ T.leftOuter.sourceCompactification.Xbar from
      T.innerToFirst) := T.innerToFirst_isOpenImmersion

local instance unboundedTripleCartesianRightLocal3 : IsOpenImmersion
    (show T.leftInner.first.Xbar ⟶ T.rightOuter.sourceCompactification.Xbar from
      T.leftInner.middleOpen ≫ T.innerToFirst) :=
  inferInstanceAs (IsOpenImmersion (T.leftInner.middleOpen ≫ T.innerToFirst))

omit hA₁ in
/-- The actual right maps retain the original final transport in a whole typed equation. -/
theorem moduleUnboundedTripleCartesianRightRoute :
    ImageRightRealizationEquation
      (K := moduleUnboundedDerivedLowerShriek T.leftInner.first.j Λ)
      (J := moduleUnboundedDerivedLowerShriek T.first.j Λ)
      (Q₀ := moduleUnboundedDerivedDirectImage Λ T.leftInner.first.p)
      (I₁ := moduleUnboundedDerivedLowerShriek T.tail.first.j Λ)
      (Q₁ := moduleUnboundedDerivedDirectImage Λ T.tail.first.p)
      (I₂ := moduleUnboundedDerivedLowerShriek T.last.j Λ)
      (M := moduleUnboundedDerivedLowerShriek T.tail.middleOpen Λ)
      (R := moduleUnboundedDerivedDirectImage Λ T.middle.p)
      (Hsrc := moduleUnboundedDerivedLowerShriek (T.tail.first.j ≫ T.tail.middleOpen) Λ)
      (Hsrc' := moduleUnboundedDerivedLowerShriek T.tail.sourceCompactification.j Λ)
      (Htgt := moduleUnboundedDerivedLowerShriek (T.leftInner.middleOpen ≫ T.innerToFirst) Λ)
      (R₀₂ := moduleUnboundedDerivedDirectImage Λ T.first.p)
      (P := moduleUnboundedDerivedDirectImage Λ T.last.p)
      (Stail := moduleUnboundedDerivedDirectImage Λ (T.middle.p ≫ T.last.p))
      (S := moduleUnboundedDerivedDirectImage Λ (T.first.p ≫ T.middle.p ≫ T.last.p))
      (S' := moduleUnboundedDerivedDirectImage Λ ((T.first.p ≫ T.middle.p) ≫ T.last.p))
      (moduleUnboundedProperOpenMate T.tail.first.p T.tail.middleOpen T.last.j T.middle.p
        T.tail.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫
        T.innerToFirst) (T.tail.first.j ≫ T.tail.middleOpen) T.first.p
        (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst) Λ)
      (moduleUnboundedDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j)
      (moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j
        (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (unboundedTripleFirstOpenEquality T))
      (moduleUnboundedDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm
      (eqToIso (congrArg (fun p : T.first.Xbar ⟶ W => moduleUnboundedDerivedDirectImage Λ p)
        (Category.assoc T.first.p T.middle.p T.last.p).symm))
      (moduleUnboundedTripleTailMap T Λ) (moduleUnboundedTripleRightOuterMap T Λ) := by
  let σb := moduleUnboundedProperOpenMate T.tail.first.p T.tail.middleOpen T.last.j T.middle.p
    T.tail.isPullback_middleOpen.flip Λ
  let σh := moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫
    T.innerToFirst) (T.tail.first.j ≫ T.tail.middleOpen) T.first.p
    (T.leftInner.isPullback_middleOpen.flip.paste_vert T.isPullback_innerToFirst) Λ
  let σh' := moduleUnboundedProperOpenMate T.leftInner.first.p (T.leftInner.middleOpen ≫
    T.innerToFirst) T.tail.sourceCompactification.j T.first.p T.isPullback_first.flip Λ
  let dh := moduleUnboundedDerivedLowerShriekCompIso Λ T.tail.middleOpen T.tail.first.j
  let e := eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ T.tail.first_j_middleOpen)
  let c := moduleUnboundedDerivedLowerShriekOverIso Λ T.leftInner.first.j
    (T.leftInner.middleOpen ≫ T.innerToFirst) T.first.j (unboundedTripleFirstOpenEquality T)
  let sTail := (moduleUnboundedDerivedDirectImageCompIso Λ T.last.p T.middle.p).symm
  let s := (moduleUnboundedDerivedDirectImageCompIso Λ (T.middle.p ≫ T.last.p) T.first.p).symm
  let ep := eqToIso (congrArg (fun p : T.first.Xbar ⟶ W => moduleUnboundedDerivedDirectImage Λ p)
    (Category.assoc T.first.p T.middle.p T.last.p).symm)
  exact imageRightRealizationEquation σb σh σh' dh e
    (moduleUnboundedTripleHorizontalOpenTransport T Λ) c sTail s ep
    (moduleUnboundedTripleTailMap T Λ) (moduleUnboundedTripleRightOuterMap T Λ) rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
