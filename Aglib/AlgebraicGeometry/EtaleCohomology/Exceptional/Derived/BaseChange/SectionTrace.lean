/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCoefficientIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity.Finite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.CategoryTheory.Sites.Representable.SectionComparisonValues
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Section
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangePastingEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange.Shift
public import Aglib.CategoryTheory.Adjunction.SectionTrace

/-! Original module coefficient values for unit and roots section rectangles. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open CategoryTheory Coefficients
universe u wX wY

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y) (ha : a ≫ r = 𝟙 X)
  (n : ℕ)
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]

/-- The actual unit comparisons retain the complete original derived section coefficient law. -/
abbrev moduleDerivedUnitSectionValue :=
  let Λ := ULift.{u + 1} (ZMod n)
  let F := moduleInverseImage r Λ
  let G := moduleInverseImage a Λ
  let P := fun f : X ⟶ X => moduleInverseImage f Λ
  let c := moduleInverseImageCompIso Λ r a
  let e := moduleInverseImageIdIso Λ X
  let u := moduleUnitInverseImageIso r n
  let v := moduleUnitInverseImageIso a n
  let q := fun f : X ⟶ X => moduleUnitInverseImageIso f n
  let cD := moduleDerivedInverseImageCompIso Λ r a
  let iD := eqToIso (congrArg (fun f : X ⟶ X => moduleDerivedInverseImage Λ f) ha) ≪≫
    moduleDerivedInverseImageIdIso Λ X
  let uD := constantModuleDerivedUnitPullbackIso r n
  let vD := constantModuleDerivedUnitPullbackIso a n
  Functor.rightDerivedSingle_sectionValue_of_original_family F G P ha c e u v q
    (moduleUnitInverseImageIso_comp r a n) (moduleUnitInverseImageIso_identity X n)
    cD iD uD vD rfl rfl
    (constantModuleDerivedUnitPullbackIso_eq r n)
    (constantModuleDerivedUnitPullbackIso_eq a n)

variable (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The actual roots comparisons retain the same derived section law at invertible level. -/
abbrev moduleDerivedRootsSectionValue :=
  let Λ := ULift.{u + 1} (ZMod n)
  let F := moduleInverseImage r Λ
  let G := moduleInverseImage a Λ
  let P := fun f : X ⟶ X => moduleInverseImage f Λ
  let c := moduleInverseImageCompIso Λ r a
  let e := moduleInverseImageIdIso Λ X
  let hY := GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible r n hinv
  let u := moduleRootsOfUnityInverseImageIso r n hn hinv
  let v := moduleRootsOfUnityInverseImageIso a n hn hY
  let q := fun f : X ⟶ X => moduleRootsOfUnityInverseImageIso f n hn hinv
  let cD := moduleDerivedInverseImageCompIso Λ r a
  let iD := eqToIso (congrArg (fun f : X ⟶ X => moduleDerivedInverseImage Λ f) ha) ≪≫
    moduleDerivedInverseImageIdIso Λ X
  let uD := moduleRootsDerivedSinglePullbackIso r n hn hinv
  let vD := moduleRootsDerivedSinglePullbackIso a n hn hY
  Functor.rightDerivedSingle_sectionValue_of_original_family F G P ha c e u v q
    (moduleRootsOfUnityInverseImageIso_comp r a n hn hinv)
    (moduleRootsOfUnityInverseImageIso_identity X n hn hinv)
    cD iD uD vD rfl rfl
    (moduleRootsDerivedSinglePullbackIso_eq r n hn hinv)
    (moduleRootsDerivedSinglePullbackIso_eq a n hn hY)

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wB wY wZ
variable (Λ : Type (u + 1)) [Ring Λ] {B Y : Scheme.{u}}
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  (p : Y ⟶ B) (b : B ⟶ B) (a : Y ⟶ Y)
  (hb : b = 𝟙 B) (ha : a = 𝟙 Y) (h : p ≫ b = a ≫ p)
  (K : DerivedCategory.Plus (ModuleSheaf Y Λ))

/-- The native horizontal identity is retained as a whole original value predicate. -/
abbrev moduleDerivedBaseChangeMapIdentityValue :=
  HorizontalIdentityValue.transport_index
    (moduleDerivedDirectImage Λ p)
    (fun a : Y ⟶ Y => moduleDerivedInverseImage Λ a)
    (fun b : B ⟶ B => moduleDerivedInverseImage Λ b)
    (fun b a => p ≫ b = a ≫ p)
    (fun b a h => moduleDerivedBaseChangeMap Λ p p b a h)
    (𝟙 Y) (𝟙 B) (moduleDerivedInverseImageIdIso Λ Y)
    (moduleDerivedInverseImageIdIso Λ B) K
    (fun h => HorizontalIdentityValue.of_mate (moduleDerivedAdjunction Λ p)
      (moduleDerivedInverseImageSquareIso Λ p p (𝟙 B) (𝟙 Y) h)
      (moduleDerivedInverseImageIdIso Λ B) (moduleDerivedInverseImageIdIso Λ Y)
      (moduleDerivedBaseChangeMap Λ p p (𝟙 B) (𝟙 Y) h) rfl
      (moduleDerivedInverseImageSquareIso_id Λ p h) K)
    a b ha hb h

variable (o : B ⟶ Y) (ho : o ≫ p = 𝟙 B)
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback p p) Λ)]
  (i : Y ⟶ pullback p p) (hi₁ : i ≫ pullback.fst p p = 𝟙 Y)
  (hi₂ : i ≫ pullback.snd p p = p ≫ o)

/-- The same section rectangle supplies the original pasting and outer identity predicates. -/
abbrev moduleDerivedBaseChangeMapSectionRectangleValues :=
  let π := pullback.snd p p
  let q := pullback.fst p p
  let e₁ : π ≫ p = q ≫ p := pullback.condition.symm
  let e₂ : p ≫ o = i ≫ π := hi₂.symm
  let e : p ≫ (o ≫ p) = (i ≫ q) ≫ p := by rw [ho, hi₁]; simp
  let hp := moduleDerivedBaseChangeMap_hComp_equation Λ p π p p o q i e₁ e₂ e K
  let hi := moduleDerivedBaseChangeMapIdentityValue Λ p (o ≫ p) (i ≫ q) ho hi₁ e K
  And.intro hp hi

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wB wY wZ
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {B Y : Scheme.{u}} (p : Y ⟶ B) (o : B ⟶ Y) (ho : o ≫ p = 𝟙 B)
  (i : Y ⟶ pullback p p) (hi₁ : i ≫ pullback.fst p p = 𝟙 Y)
  (hi₂ : i ≫ pullback.snd p p = p ≫ o)
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Y, ⊤)))
  [HasDerivedCategory.{wB} (ModuleSheaf B (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback p p) (ULift.{u + 1} (ZMod n)))]

/-- Actual exchange pasting and original roots transport around the same-curve section. -/
abbrev moduleDerivedRootsSectionExchangeLoop :=
  let Λ := ULift.{u + 1} (ZMod n)
  let π := pullback.snd p p
  let q := pullback.fst p p
  let KY := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y Λ) 0).obj
    (moduleRootsOfUnity Y n)
  let KZ := (DerivedCategory.Plus.singleFunctor (ModuleSheaf (pullback p p) Λ) 0).obj
    (moduleRootsOfUnity (pullback p p) n)
  let e₁ : π ≫ p = q ≫ p := pullback.condition.symm
  let e₂ : p ≫ o = i ≫ π := hi₂.symm
  let e : p ≫ (o ≫ p) = (i ≫ q) ≫ p := by rw [ho, hi₁]; simp
  let β₁ := moduleDerivedBaseChangeMap Λ p π p q e₁
  let β₂ := moduleDerivedBaseChangeMap Λ π p o i e₂
  let β₀ := moduleDerivedBaseChangeMap Λ p p (o ≫ p) (i ≫ q) e
  let γ := moduleDerivedInverseImageCompIso Λ p o
  let δ := moduleDerivedInverseImageCompIso Λ q i
  let eG := eqToIso (congrArg (fun f : B ⟶ B => moduleDerivedInverseImage Λ f) ho) ≪≫
    moduleDerivedInverseImageIdIso Λ B
  let eH := eqToIso (congrArg (fun f : Y ⟶ Y => moduleDerivedInverseImage Λ f) hi₁) ≪≫
    moduleDerivedInverseImageIdIso Λ Y
  let aq := moduleRootsDerivedSinglePullbackIso q n hn hinv
  let ai := moduleRootsDerivedSinglePullbackIso i n hn
    (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible q n hinv)
  let h := moduleDerivedBaseChangeMapSectionRectangleValues Λ p KY o ho i hi₁ hi₂
  let hc := moduleDerivedRootsSectionValue q i hi₁ n hn hinv
  CorrectedExchangeLoop.of_original_values β₁ β₂ β₀ γ δ eG eH KY KZ aq ai h.1 h.2 hc

end AlgebraicGeometry.Scheme.EtaleCohomology
