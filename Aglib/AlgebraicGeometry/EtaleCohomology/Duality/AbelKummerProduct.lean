/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing

/-! The original degree-one product with the original Abel boundary. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients Scheme.OverField Scheme.OverField.Curve
open Scheme.OverField.Curve.PointDivisor Scheme.Modules.Invertible
open GroupCohomology.Kummer.CoefficientBaseChange GroupCohomology.Kummer.Coefficients

universe u wX wZ wAX wAZ wDX wDZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (o : Base k ⟶ X.left) (ho : o ≫ X.hom = 𝟙 (Base k))
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hi : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback X.hom X.hom) (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X.left)]
  [HasExt.{wAZ} (AbelianSheaf.{u, u + 1} (pullback X.hom X.hom))]
  [HasDerivedCategory.{wDX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDZ} (ModuleSheaf (pullback X.hom X.hom) (ULift.{u + 1} (ZMod n)))]

include hunit in
/-- The original Abel boundary and the original diagonal boundary have the
same product against the first pullback of an original degree-one class. -/
theorem firstPullback_comp_abelModuleKummerClass (x : constantModuleExt.{u, wX} n X.left 1) :
    letI : SmoothOfRelativeDimension 1 X.hom := hX.smooth
    letI : IsProper X.hom := hX.proper
    let f := pullback.fst X.hom X.hom
    let x₁ := constantModuleExtPullback.{u, wX, wZ} n f 1 x
    x₁.comp (abelModuleKummerClass X.hom o ho n hn hi) (rfl : 1 + 2 = 3) =
      x₁.comp (diagonalModuleKummerClass X.hom n hn (levelInvertible f n hi))
        (rfl : 1 + 2 = 3) := by
  dsimp only
  let : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let : IsProper X.hom := hX.proper
  let : LocallyOfFiniteType X.hom := curveProperties_locallyOfFiniteType hX
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let f := pullback.fst X.hom X.hom
  let x₁ := constantModuleExtPullback.{u, wX, wZ} n f 1 x
  let c := (moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X.left n 2).symm
    (picardBoundary X.left n hn hi (classOf X.left (positiveSectionLineBundle X.hom o ho)))
  let : Subsingleton (Sheaf.H.{wAX} (mu X.left n) 3) :=
    Curves.roots_subsingleton_H_of_curve k X.left X.hom hX.topologicalKrullDim_eq_one.le
      n hn hunit hi 3 (by omega)
  let E := moduleRootsUnitExtCohomologyAddEquiv.{u, wX, wAX} X.left n 3
  have hc : x.comp c (rfl : 1 + 2 = 3) = 0 :=
    E.injective (Subsingleton.elim _ _)
  have hzero : x₁.comp (moduleRootsUnitExtPullback.{u, wX, wZ} f n hn hi 2 c)
      (rfl : 1 + 2 = 3) = 0 := by
    rw [← moduleRootsUnitExtPullback_comp_constant f n hn hi 1 2 3 rfl x c, hc, map_zero]
  rw [abelModuleKummerClass_eq, sub_eq_add_neg, Ext.comp_add, Ext.comp_neg,
    hzero, neg_zero, add_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
