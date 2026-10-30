/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.CategoryTheory.Functor.ComparisonPasting.ExchangeInterchange

/-! # Interchange of the original higher exchanges on relative charts

Two applications of the original horizontal-pasting equality give the square
between a base-change map and its chart-relative base-change map. Both
coefficient comparisons are the original inverse-image square isomorphisms.
The eight derived models are independent; no Cartesian or invertibility
condition is used.

The ordinary square is intrinsic. Separate compatibility companions retain the
literal original transports in all eight independently supplied derived models.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExchangeInterchange


universe u dX dS dX' dS' dZ dU dW dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem inverseImageSquareIso_inv_factor_whole {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (fT : Y ⟶ T) (a : T ⟶ S) (k : Y ⟶ X)
    (h : fT ≫ a = k ≫ f) :
    (inverseImageSquareIso f fT a k h).inv =
      (inverseImageComp f k).inv ≫
        (eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)).inv ≫
        (inverseImageComp a fT).hom :=
  natIso_inverse_factor (inverseImageSquareIso f fT a k h) (inverseImageComp a fT)
    (eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)) (inverseImageComp f k)
    (inverseImageSquareIso_eq_comp f fT a k h)

private theorem higherBaseChangeMap_transport_whole
    {X S Y T : Scheme.{u}}
            (f : X ⟶ S) (fT : Y ⟶ T) (a₁ a₂ : T ⟶ S) (k₁ k₂ : Y ⟶ X)
    (h₁ : fT ≫ a₁ = k₁ ≫ f) (h₂ : fT ≫ a₂ = k₂ ≫ f)
    (ha : a₂ = a₁) (hk : k₂ = k₁) (q : ℕ) :
    Functor.whiskerLeft (higherDirectImage f q)
        (eqToIso (congrArg (fun a : T ⟶ S => inverseImage a) ha)).inv ≫
        higherBaseChangeMap f fT a₂ k₂ h₂ q =
      higherBaseChangeMap f fT a₁ k₁ h₁ q ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun k : Y ⟶ X => inverseImage k) hk)).inv
          (higherDirectImage fT q) :=
  exchangeFamily_transport_whole
    (fun a : T ⟶ S => inverseImage a) (fun k : Y ⟶ X => inverseImage k)
    (higherDirectImage f q) (higherDirectImage fT q)
    (fun a k => fT ≫ a = k ≫ f)
    (fun a k h => higherBaseChangeMap f fT a k h q) a₁ a₂ k₁ k₂ h₁ h₂ ha hk

section Ordinary

variable {X S X' S' Z U W V : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)

/-- Whole interchange of the four original higher exchanges, before a coefficient
is chosen. Both comparisons are the original inverse-image square isomorphisms,
with an intrinsic ordinary higher map at every edge. -/
theorem higherBaseChangeMap_chartRelative_square_whole (q : ℕ) :
    ((TwoSquare.mk (higherDirectImage f q) (inverseImage g') (inverseImage g)
        (higherDirectImage f' q) (higherBaseChangeMap f f' g g' h q)).vComp
      (TwoSquare.mk (higherDirectImage f' q) (inverseImage piV) (inverseImage aV)
        (higherDirectImage fV q) (higherBaseChangeMap f' fV aV piV hV q))).whiskerRight
          (inverseImageSquareIso aU aV g b hb).inv =
      ((TwoSquare.mk (higherDirectImage f q) (inverseImage piU) (inverseImage aU)
        (higherDirectImage fU q) (higherBaseChangeMap f fU aU piU hU q)).vComp
      (TwoSquare.mk (higherDirectImage fU q) (inverseImage r) (inverseImage b)
        (higherDirectImage fV q) (higherBaseChangeMap fU fV b r hR q))).whiskerLeft
          (inverseImageSquareIso piU piV g' r hr).inv := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} Z)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} U)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} W)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} V)
  let h₁ : fV ≫ (b ≫ aU) = (r ≫ piU) ≫ f := by
    rw [← Category.assoc, hR, Category.assoc, hU, ← Category.assoc]
  let h₂ : fV ≫ (aV ≫ g) = (piV ≫ g') ≫ f := by
    rw [← Category.assoc, hV, Category.assoc, h, ← Category.assoc]
  exact twoSquare_relative_of_pastings
    (inverseImageComp aU b) (inverseImageComp g aV)
    (eqToIso (congrArg (fun a : V ⟶ S => inverseImage a) hb))
    (inverseImageComp piU r) (inverseImageComp g' piV)
    (eqToIso (congrArg (fun k : W ⟶ X => inverseImage k) hr))
    (inverseImageSquareIso aU aV g b hb).inv
    (inverseImageSquareIso piU piV g' r hr).inv
    (inverseImageSquareIso_inv_factor_whole aU aV g b hb)
    (inverseImageSquareIso_inv_factor_whole piU piV g' r hr)
    (higherBaseChangeMap f fV (b ≫ aU) (r ≫ piU) h₁ q)
    (higherBaseChangeMap f fV (aV ≫ g) (piV ≫ g') h₂ q)
    (higherHorizontalWholeLadder_pasting f fU fV aU b piU r hU hR h₁ q)
    (higherHorizontalWholeLadder_pasting f f' fV g aV g' piV h hV h₂ q)
    (higherBaseChangeMap_transport_whole f fV (b ≫ aU) (aV ≫ g)
      (r ≫ piU) (piV ≫ g') h₁ h₂ hb hr q)

/-- Interchange of the original higher exchanges, with the two literal
inverse-image square comparisons and every original coefficient map retained. -/
theorem higherBaseChangeMap_chartRelative_square (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageSquareIso aU aV g b hb).inv.app ((higherDirectImage f q).obj F) ≫
        (inverseImage aV).map ((higherBaseChangeMap f f' g g' h q).app F) ≫
        (higherBaseChangeMap f' fV aV piV hV q).app ((inverseImage g').obj F) =
      (inverseImage b).map ((higherBaseChangeMap f fU aU piU hU q).app F) ≫
        (higherBaseChangeMap fU fV b r hR q).app ((inverseImage piU).obj F) ≫
        (higherDirectImage fV q).map ((inverseImageSquareIso piU piV g' r hr).inv.app F) := by
  have hwhole := higherBaseChangeMap_chartRelative_square_whole
    f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.vComp_app, TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
    NatTrans.congr_app hwhole F

end Ordinary

section SelectedModels

variable {X S X' S' Z U W V : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{dW} (AbelianSheaf.{u, u + 1} W)]
  [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)

/-- The literal original relative square in all eight independently selected models. -/
theorem higherBaseChangeMapFromDerived_chartRelative_square_whole (q : ℕ) :
    ((TwoSquare.mk (higherDirectImage f q) (inverseImage g') (inverseImage g)
        (higherDirectImage f' q) (higherBaseChangeMapFromDerived f f' g g' h q)).vComp
      (TwoSquare.mk (higherDirectImage f' q) (inverseImage piV) (inverseImage aV)
        (higherDirectImage fV q) (higherBaseChangeMapFromDerived f' fV aV piV hV q))).whiskerRight
          (inverseImageSquareIso aU aV g b hb).inv =
      ((TwoSquare.mk (higherDirectImage f q) (inverseImage piU) (inverseImage aU)
        (higherDirectImage fU q) (higherBaseChangeMapFromDerived f fU aU piU hU q)).vComp
      (TwoSquare.mk (higherDirectImage fU q) (inverseImage r) (inverseImage b)
        (higherDirectImage fV q) (higherBaseChangeMapFromDerived fU fV b r hR q))).whiskerLeft
          (inverseImageSquareIso piU piV g' r hr).inv := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    higherBaseChangeMap_chartRelative_square_whole
      f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q

/-- The original selected-model relative square retains every coefficient component. -/
theorem higherBaseChangeMapFromDerived_chartRelative_square (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageSquareIso aU aV g b hb).inv.app ((higherDirectImage f q).obj F) ≫
        (inverseImage aV).map ((higherBaseChangeMapFromDerived f f' g g' h q).app F) ≫
        (higherBaseChangeMapFromDerived f' fV aV piV hV q).app ((inverseImage g').obj F) =
      (inverseImage b).map ((higherBaseChangeMapFromDerived f fU aU piU hU q).app F) ≫
        (higherBaseChangeMapFromDerived fU fV b r hR q).app ((inverseImage piU).obj F) ≫
        (higherDirectImage fV q).map ((inverseImageSquareIso piU piV g' r hr).inv.app F) := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    higherBaseChangeMap_chartRelative_square f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q F

end SelectedModels

end AlgebraicGeometry.Scheme.EtaleCohomology
