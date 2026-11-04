/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.GradedProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ProductDirectImageComponent

/-! The original constant-coefficient Künneth map with a proper curve factor. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct DirectSum

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wY wX wZ wEX wEY wEZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  {X : Scheme.{u}} (f : X ⟶ Base k)
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf (pullback f Y.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wEZ} (ModuleSheaf (pullback f Y.hom) (ULift.{u + 1} (ZMod n)))]

/-- The original ordered Künneth map is bijective in every total degree
with a proper smooth curve factor over an algebraically closed field. -/
abbrev constantModuleExtKunnethMap_bijective_properCurve (d : ℕ) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let Z := pullback f Y.hom
  let p := pullback.fst f Y.hom
  let q := pullback.snd f Y.hom
  let U := moduleUnit X Λ
  let V := moduleUnit Z Λ
  let rank := properCurveConstantRank (coherentGenus k Y)
  let hrank : ∀ a, 3 ≤ a → rank a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
    dsimp only [rank]
    rw [Nat.add_comm]
    rfl
  let B := constantModuleExt.{u, wEY} n Y.left
  let basis := properCurveConstantModuleExtBasis hY n hn hunit
  let hm := properCurveProductConstantDirectImageMap_isIso hY n hn hunit f
  let adj := moduleDerivedAdjunction Λ p
  let : adj.CommShift ℤ :=
    Adjunction.rightDerivedFunctorPlus_commShift (moduleInverseImageAdjunction p Λ)
  let e := (moduleInverseImage p Λ).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleUnitInverseImageIso p n)
  let x := fun a => constantModuleExtPullback.{u, wEX, wEZ} n p a
  let y := fun a => constantModuleExtPullback.{u, wEY, wEZ} n q a
  let K := constantModuleExtKunnethMap.{u, wEX, wEY, wEZ} n f Y.hom d
  let hK (a : Fin (d + 1)) (x : constantModuleExt.{u, wEX} n X a.val)
      (y : B (d - a.val)) :=
    (constantModuleExtKunnethMap_lof_tmul n f Y.hom d a x y).trans
      (constantModuleExtExternalProduct_apply n f Y.hom a.val (d - a.val) d (by omega) x y)
  Ext.bijective_orderedProduct_of_graded_components adj U V n d 3 e rank hrank
    B basis hm (fun a => x a) (fun a => y a) (constantModuleExtPullback_homPlus_singleTransport p n)
    (properCurveProductConstantDirectImageMap_component_value hY n hn hunit f) K hK

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
