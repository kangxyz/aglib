/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsAdjunctUnderlying
public import Aglib.CategoryTheory.Shift.TransportComposition

/-! Original contracted roots adjuncts under scalar forgetting. -/

open CategoryTheory CategoryTheory.Abelian

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients GroupCohomology.Kummer.Coefficients

universe u dMX dMS dAX dAS wMX wAX wMS wAS

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasDerivedCategory.{dMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{dAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dAS} (AbelianSheaf.{u, u + 1} S)]

set_option hygiene false in
local notation "Iₘ" =>
  (DerivedCategory.Plus.singleFunctor (ModuleSheaf S Λ) 0).obj (moduleUnit S Λ)

set_option hygiene false in
local notation "Kₘ" =>
  (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleRootsOfUnity X n)

/-- The original shifted map from the roots direct image under scalar forgetting. -/
abbrev moduleRootsShiftedMapUnderlying {q : ℤ}
    (t : ShiftedHom ((moduleDerivedDirectImage Λ f).obj (Kₘ)) (Iₘ) q) :=
  let e := moduleRootsDerivedDirectImageUnderlyingIso f n
  let F := SheafOfModules.toSheaf (constantRing S Λ)
  let v := (F.rightDerivedFunctorPlusSingleIso 0).app (moduleUnit S Λ)
  e.inv ≫ t.map (moduleDerivedUnderlying Λ S) ≫ v.hom⟦q⟧'

variable [HasExt.{wMX} (ModuleSheaf X Λ)] [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wMS} (ModuleSheaf S Λ)] [HasExt.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- An original module composition gives the same original abelian
cohomology value through the original integer source and roots maps. -/
abbrev moduleRootsAdjunctCompUnderlyingValue
    (p q : ℕ) {r : ℤ} (hr : r + (p : ℤ) = (q : ℤ))
    (x : Ext.{wMX} (moduleUnit X Λ) (moduleRootsOfUnity X n) p)
    (t : ShiftedHom ((moduleDerivedDirectImage Λ f).obj (Kₘ)) (Iₘ) r)
    (v : Ext.{wMS} (moduleUnit S Λ) (moduleUnit S Λ) q)
    (h : let e := constantModuleDerivedUnitPullbackIso f n
      ((moduleDerivedAdjunction Λ f).shiftedHomEquiv (p : ℤ) (Iₘ) (Kₘ)
        (e.hom ≫ x.homPlus)).comp t hr = v.homPlus) :=
  let e := constantModuleDerivedUnitPullbackIso f n
  let z := (moduleDerivedAdjunction Λ f).shiftedHomEquiv (p : ℤ) (Iₘ) (Kₘ) (e.hom ≫ x.homPlus)
  let E := moduleRootsDerivedDirectImageUnderlyingIso f n
  let F := SheafOfModules.toSheaf (constantRing S Λ)
  let w := (F.rightDerivedFunctorPlusSingleIso 0).app (moduleUnit S Λ)
  let J := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let J₀ := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj J
  let N₀ := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj (mu X n)
  let eInt := ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).app J ≪≫
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let x' := moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n p x
  let z' := (derivedImageAdjunction f).shiftedHomEquiv (p : ℤ) J₀ N₀ (eInt.hom ≫ x'.homPlus)
  let v' := etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMS, wAS} S (constantRing S Λ)
    (moduleUnit S Λ) q v
  ShiftedHom.map_comp_transport_of_values (moduleDerivedUnderlying Λ S)
    (moduleUnitDerivedIntegerMap S n) E w.hom z t hr
    v.homPlus h z' (moduleRootsAdjunctUnderlyingValue f n p x) v'.homPlus
    (moduleUnitExtCohomologyAddEquiv_homPlus S n q v)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
