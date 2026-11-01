/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LowerShriekCohomology

/-! The original source and counit square with independent Ext worlds. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open GroupCohomology.Kummer.Coefficients

universe u wM wMU wA wAU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

example (q : ℕ) :
    (moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q).toAddMonoidHom.comp
      ((Ext.mk₀ ((moduleLowerShriekAdjunction j (ULift.{u + 1} (ZMod n))).counit.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))))).precomp
          (moduleRootsOfUnity X n) (zero_add q)) =
    (Kummer.rootsCohomologyPullback j n hn hinv q).comp
      (moduleRootsUnitExtCohomologyAddEquiv X n q).toAddMonoidHom :=
  moduleLowerShriekRootsExtCohomologyAddEquiv_counit (n := n) j hn hinv q

example (q : ℕ)
    (e : Ext.{wM} ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj
      ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))))) (moduleRootsOfUnity X n) q) :
    moduleLowerShriekRootsExtCohomologyAddEquiv (n := n) j hn hinv q e =
      moduleRootsUnitExtCohomologyAddEquiv U n q
        (((Ext.mk₀ (moduleUnitInverseImageIso j n).inv).comp
          (moduleLowerShriekExtEquiv j (ULift.{u + 1} (ZMod n))
            ((moduleInverseImage j (ULift.{u + 1} (ZMod n))).obj
              (moduleUnit X (ULift.{u + 1} (ZMod n))))
            (moduleRootsOfUnity X n) q e) (zero_add q)).comp
          (Ext.mk₀ (moduleRootsOfUnityInverseImageIso j n hn hinv).hom) (add_zero q)) :=
  moduleLowerShriekRootsExtCohomologyAddEquiv_apply (n := n) j hn hinv q e

end
