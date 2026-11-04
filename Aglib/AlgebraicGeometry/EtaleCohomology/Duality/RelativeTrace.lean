/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperTopTraceBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.Shift
public import Aglib.CategoryTheory.Adjunction.SectionTrace
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Section
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.SectionTrace
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TraceTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullbackShifted

/-! Original relative product trace and its class restriction. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

/-- The exact inferred component supplies its original comparison isomorphism. -/
def originalIsoOfIsIso {C : Type*} [Category* C] {M N : C} {f : M ⟶ N}
    (h : IsIso f) : M ≅ N :=
  letI := h
  asIso f

end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wB wY wZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wB} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ}
    (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]

/-- The original invertibility witness at the self-product, before forming data. -/
abbrev properCurveProductRootsExchangeIsIso :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := Y.hom
  let KY := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
    (moduleRootsOfUnity Y.left n)
  letI : IsProper p := hY.proper
  Proper.properModuleDerivedBaseChange_isIso_zmod n hn p
    (pullback.snd p p) p (pullback.fst p p) (IsPullback.of_hasPullback p p) KY

/-- One original product trace, retaining all actual data inside the generic predicate. -/
abbrev properCurveProductTraceExistsUnique :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := Y.hom
  let π := pullback.snd p p
  let q := pullback.fst p p
  let KY := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
    (moduleRootsOfUnity Y.left n)
  let KS := (moduleDerivedDirectImage Λ p).obj KY
  let F := moduleDerivedInverseImage Λ p
  let Rπ := moduleDerivedDirectImage Λ π
  let hK := DerivedCategory.Plus.isLE_of_original_homology KS 2
    (properCurveRootsDirectImage_isZero_homology hY n hn hunit)
  let hβ := properCurveProductRootsExchangeIsIso hY n hn
  let aq := moduleRootsDerivedSinglePullbackIso q n hn (modulePoint_globalLevelInvertible n hunit)
  let u := constantModuleDerivedUnitPullbackIso p n
  F.existsUnique_originalShiftedTrace Rπ 2 hK hβ aq u
    (properCurveTopDirectImageTraceIso hY n hn hunit).hom

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open Scheme.OverField Scheme.OverField.Curve
universe u wB wY wZ
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wB} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  (o : Base k ⟶ Y.left) (ho : o ≫ Y.hom = 𝟙 (Base k))
  (i : Y.left ⟶ pullback Y.hom Y.hom)
  (hi₁ : i ≫ pullback.fst Y.hom Y.hom = 𝟙 Y.left)
  (hi₂ : i ≫ pullback.snd Y.hom Y.hom = Y.hom ≫ o)

/-- One original product trace and its exact restriction along the given rational point. -/
abbrev properCurveProductTraceExistsUniqueRestriction :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := Y.hom
  let hinv := modulePoint_globalLevelInvertible n hunit
  let hex := properCurveProductTraceExistsUnique hY n hn hunit
  let hx := moduleDerivedRootsSectionExchangeLoop p o ho i hi₁ hi₂ n hn hinv
  let hu := moduleDerivedUnitSectionValue p o ho n
  existsUnique_originalShiftedTrace_restriction_of_exists hex hx hu
    (moduleDerivedInverseImageSectionIso_commShift Λ p o ho)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open Scheme.OverField Scheme.OverField.Curve
universe u wB wY wZ wEZ
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wB} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEZ} (ModuleSheaf (pullback Y.hom Y.hom) (ULift.{u + 1} (ZMod n)))]
  (o : Base k ⟶ Y.left) (ho : o ≫ Y.hom = 𝟙 (Base k))
  (i : Y.left ⟶ pullback Y.hom Y.hom)
  (hi₁ : i ≫ pullback.fst Y.hom Y.hom = 𝟙 Y.left)
  (hi₂ : i ≫ pullback.snd Y.hom Y.hom = Y.hom ≫ o)

local instance : HasExt.{u + 2} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n))) :=
  SheafOfModules.hasExt (constantRing Y.left (ULift.{u + 1} (ZMod n)))

/-- The same original product trace restricts to the original field trace for every roots class. -/
abbrev properCurveProductTraceExistsUniqueClassRestriction :=
  let Λ := ULift.{u + 1} (ZMod n)
  let p := Y.hom
  let π := pullback.snd p p
  let q := pullback.fst p p
  let hinv := GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible q n
    (modulePoint_globalLevelInvertible n hunit)
  let hex := properCurveProductTraceExistsUniqueRestriction hY n hn hunit o ho i hi₁ hi₂
  existsUnique_originalTrace_classRestriction hex
    (fun w : Ext.{wEZ} (moduleUnit (pullback p p) Λ) (moduleRootsOfUnity (pullback p p) n) 2 =>
      moduleRootsUnitExtPullbackShiftedMateValue π p o i hi₂.symm n hn hinv 2 w)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
