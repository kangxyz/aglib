/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! The original roots pullback on native bounded-below Ext arrows. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wDX wDU wX wU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X U : Scheme.{u}} (f : U ⟶ X) (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasDerivedCategory.{wDX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wDU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- The original derived comparison for the single of the roots coefficient. -/
@[no_expose]
def moduleRootsDerivedSinglePullbackIso :=
  (moduleInverseImage f (ULift.{u + 1} (ZMod n))).rightDerivedFunctorPlusSingleIsoOfIso 0
    (moduleRootsOfUnityInverseImageIso f n hn hinv)

/-- The roots comparison is the original degree-zero single coefficient transport. -/
theorem moduleRootsDerivedSinglePullbackIso_eq :
    moduleRootsDerivedSinglePullbackIso f n hn hinv =
      (moduleInverseImage f (ULift.{u + 1} (ZMod n))).rightDerivedFunctorPlusSingleIsoOfIso 0
        (moduleRootsOfUnityInverseImageIso f n hn hinv) := by
  unfold moduleRootsDerivedSinglePullbackIso
  rfl

variable [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- The literal original roots Ext pullback in native shifted Hom coordinates. -/
theorem moduleRootsUnitExtPullback_homPlus (q : ℕ)
    (x : Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleRootsOfUnity X n) q) :
    (moduleRootsUnitExtPullback.{u, wX, wU} f n hn hinv q x).homPlus =
      ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).rightDerivedFunctorPlusSingleIsoOfIso 0
        (moduleUnitInverseImageIso f n)).inv ≫
      x.homPlus.map (moduleDerivedInverseImage (ULift.{u + 1} (ZMod n)) f) ≫
        (moduleRootsDerivedSinglePullbackIso f n hn hinv).hom⟦(q : ℤ)⟧' := by
  rw [moduleRootsUnitExtPullback_apply, moduleUnitExtPullback_apply]
  exact (moduleInverseImage f (ULift.{u + 1} (ZMod n))).mapExactFunctor_transport_homPlus
    (moduleUnitInverseImageIso f n) (moduleRootsOfUnityInverseImageIso f n hn hinv) q x

end AlgebraicGeometry.Scheme.EtaleCohomology
