/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProductDirectImage

/-! The original homogeneous components of the transported product splitting. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wY wX wZ wEY wEZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  {X : Scheme.{u}} (f : X ⟶ Base k)
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback f Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEZ} (ModuleSheaf (pullback f Y.hom) (ULift.{u + 1} (ZMod n)))]

/-- Each original product component is the original regraded adjunct of the
pullback of the corresponding original right-factor basis class. -/
abbrev properCurveProductConstantDirectImageMap_component_value :=
  fun i : ProperCurveGradeIndex (coherentGenus k Y) =>
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Base k
    let p := pullback.fst f Y.hom
    let q := pullback.snd f Y.hom
    let g := Y.hom
    let sq := (IsPullback.of_hasPullback f Y.hom).flip
    let e := (moduleInverseImage g Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
      (moduleUnitInverseImageIso g n)
    let v := (moduleInverseImage q Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
      (moduleUnitInverseImageIso q n)
    let d := i.1.val
    let η := ((DerivedCategory.Plus.singleFunctors (ModuleSheaf S Λ)).shiftIso
      (-(d : ℤ)) (d : ℤ) 0 (by omega)).app (moduleUnit S Λ)
    let η' := ((DerivedCategory.Plus.singleFunctors (ModuleSheaf X Λ)).shiftIso
      (-(d : ℤ)) (d : ℤ) 0 (by omega)).app (moduleUnit X Λ)
    let b := properCurveConstantModuleExtBasis hY n hn hunit d i.2
    let y := constantModuleExtPullback.{u, wEY, wEZ} n q d b
    let hx := properCurveConstantDirectImageSplitComponent_hom_value hY n hn hunit i
    let h := constantModuleExtPullback_shiftedMateValue g p f q sq.w.symm n d b
    let e' := (moduleInverseImage p Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
      (moduleUnitInverseImageIso p n)
    let u := (moduleInverseImage f Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
      (moduleUnitInverseImageIso f n)
    let I := ProperCurveGradeIndex (coherentGenus k Y)
    let P := moduleFieldDerivedFreeSplitUnits k Λ (properCurveGradeDegree (genus :=
      coherentGenus k Y))
    let Q (j : I) := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ)
      (properCurveGradeDegree j)).obj (moduleUnit X Λ)
    let a (j : I) := properCurveProductUnitGradeIso f n (properCurveGradeDegree j)
    let K := properCurveConstantDirectImage (X := Y) n
    let c := moduleFieldDerivedFreeSplitComponent k Λ properCurveGradeDegree K
      (properCurveConstantDirectImageGradedBasis hY n hn hunit)
    regradedComponent_of_shiftedMateValue_biproduct
      (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ p)
      (moduleDerivedBaseChangeMap Λ g p f q sq.w.symm) e e' u v b.homPlus y.homPlus h
      P Q i a η η' rfl c hx (properCurveConstantDirectImageSplitIso hY n hn hunit).hom
      (properCurveConstantDirectImageSplitIso_hom hY n hn hunit)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
