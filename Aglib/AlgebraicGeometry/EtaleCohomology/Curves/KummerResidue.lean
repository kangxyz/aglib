/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LocalUnits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootNaturality
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Curves.Picard.GenericPower
public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Mathlib.Data.ZMod.Basic

/-! # Original Kummer residue maps

The original generic-point pullback, positive field-unit quotient equivalence,
and actual function-field identification for an open immersion define residue
as local order modulo the level. No properness, finite boundary, global-unit
root-surjectivity or residue exactness premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange
open GroupCohomology.Kummer.Torsor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidue

universe u w w'

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X] [IsNoetherian X]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Original integer order after the actual inverse function-field identification. -/
def boundaryOrder (x : ClosedPoint X) : Additive U.functionFieldˣ →+ ℤ :=
  (Scheme.OverField.Curve.Divisors.localOrder X x).comp
    ((Units.mapEquiv (Scheme.FunctionField.fieldEquiv j).symm.toMulEquiv).toAdditive).toAddMonoidHom

/-- Actual order modulo the level annihilates every nth power. -/
theorem boundaryOrder_mod_nsmul (x : ClosedPoint X) (n : ℕ)
    (a : Additive U.functionFieldˣ) :
    (boundaryOrder j x (n • a) : ZMod n) = 0 := by
  change ((Int.castAddHom (ZMod n)).comp (boundaryOrder j x)) (n • a) = 0
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The native quotient of function-field units maps to original order modulo n. -/
def orderModuloPowers (x : ClosedPoint X) (n : ℕ) :
    Additive U.functionFieldˣ ⧸
        (nsmulAddMonoidHom (α := Additive U.functionFieldˣ) n).range →+ ZMod n :=
  QuotientAddGroup.lift _ ((Int.castAddHom (ZMod n)).comp (boundaryOrder j x)) (by
    rintro _ ⟨a, rfl⟩
    exact boundaryOrder_mod_nsmul j x n a)

/-- The quotient map retains the literal local order of each unit representative. -/
@[simp] theorem orderModuloPowers_mk (x : ClosedPoint X) (n : ℕ)
    (a : Additive U.functionFieldˣ) :
    orderModuloPowers j x n (QuotientAddGroup.mk a) =
      (boundaryOrder j x a : ZMod n) := rfl

section Field

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec U.functionField, ⊤)))

/-- Residue on original function-field H1, through its positive unit quotient. -/
def fieldResidue (x : ClosedPoint X) :
    H1Etale (Spec U.functionField) (mu (Spec U.functionField) n) →+ ZMod n :=
  (orderModuloPowers j x n).comp
    (Kummer.localUnitQuotientRootEquiv U.functionField n hn hinv).symm.toAddMonoidHom

/-- The original positive root class has its original order as residue, with no sign choice. -/
theorem fieldResidue_rootClass (x : ClosedPoint X) (a : Additive U.functionFieldˣ) :
    fieldResidue j n hn hinv x
      (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec U.functionField) n hn hinv
        ((Kummer.ringGlobalUnitsEquiv U.functionField a).toMul)) =
      (boundaryOrder j x a : ZMod n) := by
  exact congrArg (orderModuloPowers j x n)
    ((Kummer.localUnitQuotientRootEquiv U.functionField n hn hinv).symm_apply_apply
      (QuotientAddGroup.mk a))

end Field

section Scheme

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(U, ⊤)))

/-- Original generic-point cohomology pullback followed by original field residue. -/
def residue (x : ClosedPoint X) : H1Etale U (mu U n) →+ ZMod n :=
  (fieldResidue j n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) x).comp
      (h1Map (U.fromSpecStalk (genericPoint U)) n hn hinv)

/-- The original positive unit class pulls back before taking its field-unit residue. -/
theorem residue_rootClass (x : ClosedPoint X) (a : Γ(U, ⊤)ˣ) :
    residue j n hn hinv x
      (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity U n hn hinv a) =
    fieldResidue j n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) x
      (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec U.functionField) n hn
        (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
        (GroupCohomology.Kummer.RootNaturality.pulledUnit
          (U.fromSpecStalk (genericPoint U)) a)) :=
  congrArg (fieldResidue j n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) x)
      (GroupCohomology.Kummer.RootNaturality.rootClass_pullback
        (U.fromSpecStalk (genericPoint U)) n hn hinv a)

section DivisorPairs

open Scheme.Modules.Invertible
open Scheme.OverField.Curve.Picard

variable [IsNoetherian U]
  [∀ y : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk y.val)]

/-- Original generic-point restriction of a divisor-pair class is the positive
root class of its actual rational function, with the original Gamma-Spec coordinate. -/
theorem genericPullback_divisorPair (hdim : topologicalKrullDim U ≤ 1)
    (p : KummerPairs.pairs U n) :
    h1Map (U.fromSpecStalk (genericPoint U)) n hn hinv
      (torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
        U n hn hinv (TrivializedPower.ofDivisorPair U hdim n p))) =
    rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
      (Spec U.functionField) n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
      ((Kummer.ringGlobalUnitsEquiv U.functionField p.val.2).toMul) := by
  refine (PowerBaseChange.h1Map_torsor EtaleDescent.etaleLineBundleDescent
    (U.fromSpecStalk (genericPoint U)) n hn hinv
      (TrivializedPower.ofDivisorPair U hdim n p)).trans ?_
  refine (torsorExtClass_iso (KummerH1.pairTorsorIso EtaleDescent.etaleLineBundleDescent
    (Spec U.functionField) n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
      (Q := PowerRoot.unitPair (Spec U.functionField) n
        ((Kummer.ringGlobalUnitsEquiv U.functionField p.val.2).toMul))
      (GenericTrivialization.genericIso U hdim p.val.1) ?_)).trans
    (PowerRoot.torsorExtClass_unitPair EtaleDescent.etaleLineBundleDescent
      (Spec U.functionField) n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) _)
  have hunit : (Kummer.ringGlobalUnitsEquiv U.functionField p.val.2).toMul =
      Units.map (Scheme.ΓSpecIso U.functionField).inv.hom.toMonoidHom p.val.2.toMul := by
    apply Units.ext
    rfl
  simpa only [PowerRoot.unitPair, Iso.trans_hom, Category.assoc,
    ScalarAutomorphisms.scalarIso, hunit] using
    GenericPower.genericDivisorPair_compatibility U hdim n p

/-- Original residue of an actual divisor-pair H1 class is the boundary order
of its original function representative modulo n. No root choice enters. -/
theorem residue_divisorPair (hdim : topologicalKrullDim U ≤ 1)
    (x : ClosedPoint X) (p : KummerPairs.pairs U n) :
    residue j n hn hinv x
      (torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
        U n hn hinv (TrivializedPower.ofDivisorPair U hdim n p))) =
      (boundaryOrder j x p.val.2 : ZMod n) :=
  (congrArg (fieldResidue j n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) x)
      (genericPullback_divisorPair n hn hinv hdim p)).trans
    (fieldResidue_rootClass j n hn
      (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv) x p.val.2)

end DivisorPairs

end Scheme

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidue
