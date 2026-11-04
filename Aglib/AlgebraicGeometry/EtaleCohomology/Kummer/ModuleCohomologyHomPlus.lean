/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! The original scalar-forgetting comparison on native shifted Ext arrows. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients GroupCohomology.Kummer.Coefficients

universe u wM wA dM dA

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (n : ℕ)
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{dA} (AbelianSheaf.{u, u + 1} X)]

/-- The original integer source of the scalar-forgetting map, in the derived category. -/
abbrev moduleUnitDerivedIntegerMap :=
  let Λ := ULift.{u + 1} (ZMod n)
  let R := constantRing X Λ
  let F := SheafOfModules.toSheaf R
  let S := DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0
  S.map (Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal R) ≫
    (F.rightDerivedFunctorPlusSingleIso 0).inv.app (moduleUnit X Λ)

/-- Scalar forgetting identifies the original shifted map of a roots class. -/
theorem moduleRootsUnitExtCohomologyAddEquiv_homPlus (q : ℕ)
    (x : Ext.{wM} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :
    let Λ := ULift.{u + 1} (ZMod n)
    let R := constantRing X Λ
    let F := SheafOfModules.toSheaf R
    let e := F.rightDerivedFunctorPlusSingleIsoOfIso 0 (moduleRootsOfUnityUnderlyingIso X n)
    (moduleRootsUnitExtCohomologyAddEquiv.{u, wM, wA} X n q x).homPlus =
      moduleUnitDerivedIntegerMap X n ≫ x.homPlus.map (moduleDerivedUnderlying Λ X) ≫
        e.hom⟦(q : ℤ)⟧' := by
  intro Λ R F e
  rw [moduleRootsUnitExtCohomologyAddEquiv_apply, moduleUnitExtAddEquiv_apply]
  let a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F.obj (moduleUnit X Λ) :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal R
  let b : F.obj (moduleRootsOfUnity X n) ⟶ mu X n := (moduleRootsOfUnityUnderlyingIso X n).hom
  change (((Ext.mk₀ a).comp (x.mapExactFunctor F) (zero_add q)).comp
    (Ext.mk₀ b) (add_zero q)).homPlus = _
  let S := DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0
  let e₀ := F.rightDerivedFunctorPlusSingleIso 0
  let u := S.map a
  let v := e₀.inv.app (moduleUnit X Λ)
  let w := x.homPlus.map (moduleDerivedUnderlying Λ X) ≫ e.hom⟦(q : ℤ)⟧'
  have h := F.mapExactFunctor_prePost_homPlus a b q x
  exact h.trans (Category.assoc u v w).symm

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u dM dA wM wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (n : ℕ)

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasDerivedCategory.{dM} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{dA} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wM} (ModuleSheaf X Λ)] [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

/-- The original unit-class comparison is the original shifted forgetting map
with its integer source and unit target. -/
theorem moduleUnitExtCohomologyAddEquiv_homPlus (q : ℕ)
    (x : Ext.{wM} (moduleUnit X Λ) (moduleUnit X Λ) q) :
    let F := SheafOfModules.toSheaf (constantRing X Λ)
    let e := (F.rightDerivedFunctorPlusSingleIso 0).app (moduleUnit X Λ)
    (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wM, wA} X (constantRing X Λ)
      (moduleUnit X Λ) q x).homPlus =
    moduleUnitDerivedIntegerMap X n ≫ x.homPlus.map (moduleDerivedUnderlying Λ X) ≫
      e.hom⟦(q : ℤ)⟧' := by
  intro F e
  let U := moduleUnit X Λ
  let a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F.obj U :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal (constantRing X Λ)
  let c := (Ext.mk₀ a).comp (x.mapExactFunctor F) (zero_add q)
  let S := DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0
  let r := x.homPlus.map (moduleDerivedUnderlying Λ X)
  have h := F.mapExactFunctor_prePost_homPlus a (𝟙 (F.obj U)) q x
  have hc : c.comp (Ext.mk₀ (𝟙 (F.obj U))) (add_zero q) = c :=
    Ext.comp_mk₀_id c
  have he : e.hom ≫ S.map (𝟙 (F.obj U)) = e.hom :=
    (congrArg (fun d => e.hom ≫ d) (S.map_id (F.obj U))).trans (Category.comp_id e.hom)
  change c.homPlus = (S.map a ≫ e.inv) ≫ r ≫ e.hom⟦(q : ℤ)⟧'
  refine ((congrArg Ext.homPlus hc).symm.trans h).trans ?_
  have he' := congrArg (fun b => S.map a ≫ e.inv ≫ r ≫ b⟦(q : ℤ)⟧') he
  exact he'.trans (Category.assoc (S.map a) e.inv (r ≫ e.hom⟦(q : ℤ)⟧')).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
