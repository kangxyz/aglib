/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RootsTensorOne
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.PullbackComposition

/-! Original pullback of the signed roots tensor product. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.OverField

universe u wX wZ wU wAX wAZ wAU wDX wDZ wDU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

set_option hygiene false in
local notation "ℛ" Z => ModuleCat.Sheaf.ConstantRing.commutativeSheaf
  (Scheme.smallEtaleTopology Z) Λ

section Pullback

variable {X Z : Scheme.{u}} (p : X ⟶ Base k) (f : Z ⟶ X)
  (hi : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wX} (ModuleSheaf X Λ)] [HasExt.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wDX} (ModuleSheaf X Λ)] [HasDerivedCategory.{wDZ} (ModuleSheaf Z Λ)]

/-- The original root tensor action after pullback is the negative original
ordered Yoneda product pulled back through the original roots comparison. -/
theorem moduleRootsExtOneTensor_pullback_comp
    (x : constantModuleExt.{u, wX} n X 1)
    (y : Ext.{wX} (moduleUnit X Λ) (moduleRootsOfUnity X n) 1) :
    let x₁ := constantModuleExtPullback.{u, wX, wZ} n f 1 x
    let y₁ := moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 1 y
    y₁.comp (moduleRootsExtOneTensor n hn hu (f ≫ p) x₁) (rfl : 1 + 1 = 2) =
      moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 2 (-(x.comp y (rfl : 1 + 1 = 2))) := by
  intro x₁ y₁
  let a := moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 2
  have hp : a (x.comp y (rfl : 1 + 1 = 2)) = x₁.comp y₁ (rfl : 1 + 1 = 2) :=
    moduleRootsUnitExtPullback_comp_constant f n hn hi 1 1 2 rfl x y
  have hs := comp_rootsExtOne_eq_neg_tensor n hn hu (f ≫ p) x₁ y₁
  rw [map_neg, hp, hs, neg_neg]

end Pullback

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
