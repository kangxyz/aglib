/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomologyHomPlus
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.DerivedPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare

/-! # The original derived integer source under scalar forgetting and inverse image -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem source_forward_of_inverse {C : Type*} [Category* C]
    {A B D E T : C} (a : A ⟶ B) (b : D ⟶ E)
    (z : A ≅ D) (t : T ≅ B) (e : T ≅ E)
    (h : b ≫ e.inv ≫ t.hom = z.inv ≫ a) :
    a ≫ t.inv ≫ e.hom = z.hom ≫ b := by
  have hh := congrArg (fun k => z.hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at hh
  rw [← hh]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

section Generic

universe uA vA dA uB vB dB uC vC dC uD vD dD
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{dA} A] [EnoughInjectives A]
  [HasDerivedCategory.{dB} B] [EnoughInjectives B]
  [HasDerivedCategory.{dC} C] [EnoughInjectives C]
  [HasDerivedCategory.{dD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [F.PreservesHomology] [H.PreservesHomology]
  [G.PreservesHomology] [V.PreservesHomology]
  (α : G ⋙ V ⟶ F ⋙ H)
  (αD : G.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ⟶
    F.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus)

/-- An actual ordinary source square transports through the original exact-single square. -/
private theorem integer_source_single_square (M : A) (N : B) (U : C) (W : D)
    (a : U ⟶ G.obj M) (b : W ⟶ H.obj N) (e : F.obj M ≅ N) (z : V.obj U ≅ W)
    (hs : SingleComparisonSquareEquation F H G V α αD M)
    (h : V.map a ≫ α.app M ≫ H.map e.hom = z.hom ≫ b) :
    V.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map a ≫
          (G.rightDerivedFunctorPlusSingleIso 0).inv.app M) ≫
      αD.app ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
      H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusSingleIsoOfIso 0 e).hom =
    ((V.rightDerivedFunctorPlusSingleIso 0).hom.app U ≫
      (DerivedCategory.Plus.singleFunctor D 0).map z.hom) ≫
        (DerivedCategory.Plus.singleFunctor D 0).map b ≫
        (H.rightDerivedFunctorPlusSingleIso 0).inv.app N := by
  let SD := DerivedCategory.Plus.singleFunctor D 0
  have hH := (H.rightDerivedFunctorPlusSingleIso 0).hom.naturality e.hom
  change H.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor B 0).map e.hom) ≫
      (H.rightDerivedFunctorPlusSingleIso 0).hom.app N =
    (H.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M) ≫
      SD.map (H.map e.hom) at hH
  have hV := (V.rightDerivedFunctorPlusSingleIso 0).hom.naturality a
  change V.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map a) ≫
      (V.rightDerivedFunctorPlusSingleIso 0).hom.app (G.obj M) =
    (V.rightDerivedFunctorPlusSingleIso 0).hom.app U ≫ SD.map (V.map a) at hV
  dsimp only [SingleComparisonSquareEquation] at hs
  apply (cancel_mono ((H.rightDerivedFunctorPlusSingleIso 0).hom.app N)).mp
  simp only [Functor.rightDerivedFunctorPlusSingleIsoOfIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  rw [hH, reassoc_of% hs]
  rw [← V.rightDerivedFunctorPlus.map_comp_assoc
      ((G.rightDerivedFunctorPlusSingleIso 0).inv.app M)
      ((G.rightDerivedFunctorPlusSingleIso 0).hom.app M),
    Iso.inv_hom_id_app, V.rightDerivedFunctorPlus.map_id, Category.id_comp, reassoc_of% hV]
  rw [← SD.map_comp_assoc (V.map a) (α.app M), ← SD.map_comp,
    Category.assoc, h, SD.map_comp]
  exact congrArg (fun k => (V.rightDerivedFunctorPlusSingleIso 0).hom.app U ≫
    SD.map z.hom ≫ k) (Category.comp_id (SD.map b)).symm

end Generic

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u dMX dMY dAX dAY
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
  [HasDerivedCategory.{dMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{dMY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{dAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dAY} (AbelianSheaf.{u, u + 1} Y)]

/-- Scalar forgetting and inverse image preserve the original derived integer source,
with the original constant-integer transport, for every level including zero and one. -/
theorem moduleUnitDerivedIntegerMap_inverseImage :
    let Λ := ULift.{u + 1} (ZMod n)
    let I_X := (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj
      (moduleUnit X Λ)
    let Z_X := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let eℤ := ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).app Z_X ≪≫
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).mapIso
        ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (derivedInverseImage f).map (moduleUnitDerivedIntegerMap X n) ≫
      (moduleDerivedInverseImageUnderlyingIso Λ f).inv.app I_X ≫
      (moduleDerivedUnderlying Λ Y).map (constantModuleDerivedUnitPullbackIso f n).hom =
    eℤ.hom ≫ moduleUnitDerivedIntegerMap Y n := by
  intro Λ I_X Z_X eℤ
  let M := moduleUnit X Λ
  let N := moduleUnit Y Λ
  let F := moduleInverseImage f Λ
  let H := SheafOfModules.toSheaf (constantRing Y Λ)
  let G := SheafOfModules.toSheaf (constantRing X Λ)
  let V := inverseImage f
  let W := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let a : Z_X ⟶ G.obj M :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal (constantRing X Λ)
  let b : W ⟶ H.obj N :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal (constantRing Y Λ)
  let e := moduleUnitInverseImageIso f n
  let z := (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let t := moduleInverseImageUnderlyingIso Λ f
  let β := moduleDerivedInverseImageUnderlyingIso Λ f
  have hs : SingleComparisonSquareEquation F H G V t.inv β.inv M :=
    singleComparisonSquareEquation F H G V t.inv β.inv M
      (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ f
        ((CochainComplex.singleFunctorPlus (ModuleSheaf X Λ) 0).obj M))
  have h : V.map a ≫ t.inv.app M ≫ H.map e.hom = z.hom ≫ b :=
    source_forward_of_inverse (V.map a) b z (t.app M) (H.mapIso e)
      (liftedUnitIntegerMap_inverseImage f n)
  rw [constantModuleDerivedUnitPullbackIso_eq]
  exact integer_source_single_square F H G V t.inv β.inv M N Z_X W a b e z hs h

end AlgebraicGeometry.Scheme.EtaleCohomology
