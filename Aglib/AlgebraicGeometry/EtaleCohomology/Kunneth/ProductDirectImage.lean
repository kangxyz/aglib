/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProperCurveDirectImageSplit

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.CategoryTheory.Shift.BiproductTransport

/-! The original relative constant direct image of a product with a proper curve. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- Composition with the specified surrounding isomorphisms preserves invertibility. -/
theorem CategoryTheory.isIso_comp_of_isos {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) {d : E ⟶ F} (h : IsIso d) (e : F ≅ G) :
    IsIso (a.hom ≫ b.hom ≫ c.hom ≫ d ≫ e.hom) := by
  let := h
  infer_instance

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wY wX wZ wE

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The original grade-unit comparison is obtained by shifting the actual degree-zero unit. -/
abbrev properCurveProductUnitGradeIso {S X : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
    [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))] (q : ℤ) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let eS := ((DerivedCategory.Plus.singleFunctors (ModuleSheaf S Λ)).shiftIso (-q) q 0
    (by omega)).app (moduleUnit S Λ)
  let eX := ((DerivedCategory.Plus.singleFunctors (ModuleSheaf X Λ)).shiftIso (-q) q 0
    (by omega)).app (moduleUnit X Λ)
  (moduleDerivedInverseImage Λ f).shiftedSingleIsoOfIso q eS eX
    ((moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
      (moduleUnitInverseImageIso f n))

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  {X : Scheme.{u}} (f : X ⟶ Base k)
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback f Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wE} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]

/-- The native graded splitting on the actual product, transported by proper base change. -/
abbrev properCurveProductConstantDirectImageMap :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := pullback.fst f Y.hom
  let q := pullback.snd f Y.hom
  let R := moduleDerivedDirectImage Λ p
  let F := moduleDerivedInverseImage Λ f
  let I := ProperCurveGradeIndex (coherentGenus k Y)
  let d : I → ℤ := properCurveGradeDegree
  let s := moduleFieldDerivedFreeSplitUnits k Λ d
  let a (i : I) := properCurveProductUnitGradeIso f n (d i)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj (moduleUnit Y.left Λ)
  let sq := (IsPullback.of_hasPullback f Y.hom).flip
  let bc := (moduleDerivedBaseChangeMap Λ Y.hom p f q sq.w.symm).app K
  let e := (moduleInverseImage q Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso q n)
  F.transportBiproduct s _ a (properCurveConstantDirectImageSplitIso hY n hn hunit).hom
    (bc ≫ R.map e.hom)

/-- The actual product splitting is invertible by the original proper exchange. -/
abbrev properCurveProductConstantDirectImageMap_isIso :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := pullback.fst f Y.hom
  let q := pullback.snd f Y.hom
  let R := moduleDerivedDirectImage Λ p
  let F := moduleDerivedInverseImage Λ f
  let I := ProperCurveGradeIndex (coherentGenus k Y)
  let d : I → ℤ := properCurveGradeDegree
  let s := moduleFieldDerivedFreeSplitUnits k Λ d
  let a (i : I) := properCurveProductUnitGradeIso f n (d i)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj (moduleUnit Y.left Λ)
  let sq := (IsPullback.of_hasPullback f Y.hom).flip
  letI : IsProper Y.hom := hY.proper
  let h := Proper.properModuleDerivedBaseChange_isIso_zmod n hn Y.hom p f q sq K
  let e := (moduleInverseImage q Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso q n)
  isIso_comp_of_isos (biproduct.mapIso a).symm (F.mapBiproduct s).symm
    (F.mapIso (properCurveConstantDirectImageSplitIso hY n hn hunit)) h (R.mapIso e)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
