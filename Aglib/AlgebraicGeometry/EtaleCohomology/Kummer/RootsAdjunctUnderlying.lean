/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingIntegerUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingShiftedAdjunct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomologyHomPlus
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.TransportedSources

/-! The original roots adjunct and trace coefficient under scalar forgetting. -/

open CategoryTheory CategoryTheory.Abelian

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients GroupCohomology.Kummer.Coefficients

universe u dMX dMS dAX dAS wMX wAX

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasDerivedCategory.{dMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{dAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dAS} (AbelianSheaf.{u, u + 1} S)]

/-- The original roots direct image has the original abelian roots image underneath. -/
abbrev moduleRootsDerivedDirectImageUnderlyingIso :=
  let F := SheafOfModules.toSheaf (constantRing X Λ)
  let e := F.rightDerivedFunctorPlusSingleIsoOfIso 0 (moduleRootsOfUnityUnderlyingIso X n)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj (moduleRootsOfUnity X n)
  (moduleDerivedDirectImageUnderlyingIso Λ f).app K ≪≫ (derivedDirectImage f).mapIso e

variable [HasExt.{wMX} (ModuleSheaf X Λ)] [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]

/-- The abelian roots adjunct is the original module adjunct with the original
integer source and roots direct-image comparison. -/
abbrev moduleRootsAdjunctUnderlyingValue (q : ℕ)
    (x : Ext.{wMX} (moduleUnit X Λ) (moduleRootsOfUnity X n) q) :=
  let F := SheafOfModules.toSheaf (constantRing X Λ)
  let eRoots := F.rightDerivedFunctorPlusSingleIsoOfIso 0 (moduleRootsOfUnityUnderlyingIso X n)
  let e := constantModuleDerivedUnitPullbackIso f n
  let J := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let eInt := ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).app J ≪≫
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let s := TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv
  let d := (moduleDerivedDirectImageUnderlyingIso Λ f).hom
  letI : NatTrans.CommShift d ℤ := moduleDerivedDirectImageUnderlyingIso_commShift Λ f
  let y := moduleRootsUnitExtCohomologyAddEquiv.{u, wMX, wAX} X n q x
  shiftedHomEquiv_of_mate_of_transported_sources (moduleDerivedAdjunction Λ f)
    (derivedImageAdjunction f) s d (mate_moduleDerivedInverseImageUnderlyingIso_inv Λ f)
    e.hom eInt.hom (moduleUnitDerivedIntegerMap S n) (moduleUnitDerivedIntegerMap X n)
    eRoots.hom x.homPlus y.homPlus (moduleUnitDerivedIntegerMap_inverseImage f n)
    (moduleRootsUnitExtCohomologyAddEquiv_homPlus X n q x)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
