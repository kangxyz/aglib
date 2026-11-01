/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LocalUnits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.PullbackComposition
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap

/-! # Original positive generic representatives under dominant pullback

The actual generic-point square, the original Kummer pullback composition,
and positive-root naturality transport a given generic representative along
any dominant morphism of integral schemes. The Gamma-Spec coordinate is the
original one. Source, target and both generic-point Ext universes are independent.
No open immersion, normality, curve, divisor, or global-unit root condition is
needed. The open-curve extension consumer delegates to this complete proof.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer (ringGlobalUnitsEquiv h1Map_comp)
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

namespace GroupCohomology.Kummer.Torsor

universe u wX wU wKX wKU

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  (j : U ⟶ X) [IsDominant j]

/-- The original field-unit scalar coordinate commutes with the original generic field map. -/
theorem genericFieldUnit_coordinate (a : X.functionFieldˣ) :
    GroupCohomology.Kummer.RootNaturality.pulledUnit
      (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap j)))
      ((ringGlobalUnitsEquiv X.functionField (Additive.ofMul a)).toMul) =
    (ringGlobalUnitsEquiv U.functionField
      (Additive.ofMul (Scheme.functionFieldUnitMap j a))).toMul := by
  apply Units.ext
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Scheme.functionFieldMap j))).symm
      (a : X.functionField)

variable [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wU} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{wKX} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]
  [HasExt.{wKU} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Original pullback along any dominant morphism transports the actual positive
generic root representative through its original function-field map. -/
theorem genericPullback_rootRepresentative
    (c : H1Etale X (mu X n)) (a : X.functionFieldˣ)
    (ha : h1Map (X.fromSpecStalk (genericPoint X)) n hn hinv c =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec X.functionField) n hn
        (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)
        ((ringGlobalUnitsEquiv X.functionField (Additive.ofMul a)).toMul)) :
    h1Map (U.fromSpecStalk (genericPoint U)) n hn (levelInvertible j n hinv)
        (h1Map j n hn hinv c) =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec U.functionField) n hn
        (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv))
        ((ringGlobalUnitsEquiv U.functionField
          (Additive.ofMul (Scheme.functionFieldUnitMap j a))).toMul) := by
  refine (h1Map_comp j (U.fromSpecStalk (genericPoint U)) n hn hinv c).symm.trans ?_
  refine (congrArg (fun f => h1Map f n hn hinv c)
    (Scheme.fromSpecStalk_genericPoint_naturality j)).trans ?_
  refine (h1Map_comp (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap j))) n hn hinv c).trans ?_
  refine (congrArg (h1Map (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap j))) n hn
    (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)) ha).trans ?_
  refine (GroupCohomology.Kummer.RootNaturality.rootClass_pullback
    (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap j))) n hn
    (levelInvertible (X.fromSpecStalk (genericPoint X)) n hinv)
    ((ringGlobalUnitsEquiv X.functionField (Additive.ofMul a)).toMul)).trans ?_
  exact congrArg (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
    (Spec U.functionField) n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n (levelInvertible j n hinv)))
      (genericFieldUnit_coordinate j a)

end GroupCohomology.Kummer.Torsor
