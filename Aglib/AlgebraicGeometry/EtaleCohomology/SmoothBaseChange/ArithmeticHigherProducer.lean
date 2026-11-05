/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ArithmeticCurveDegree
public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticRankDegreeProducer

/-! # Outer degree induction for arithmetic smooth-curve injective vanishing

The proved H1 theorem starts the degree induction. For each higher degree,
strictly lower arithmetic vanishing supplies the actual open-summand Leray
inputs; the independent coefficient-rank induction supplies all ranks. The
original arbitrary-point and native higher-image converters close that degree.
No external lower-degree or lower-rank hypothesis remains in the endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Every positive original higher image of the pulled-back genuine injective
vanishes on an arithmetic smooth relative curve. -/
theorem arithmeticCurveModuleInjectiveVanishing_positive (q : ℕ) (hq : 0 < q) :
    ArithmeticCurveModuleInjectiveVanishing.{u} q := by
  revert hq
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases hq1 : q = 1
    · subst q
      exact arithmeticCurveModuleInjectiveVanishing_one
    have hq2 : 2 ≤ q := by omega
    have hlower : ∀ r : ℕ, 1 ≤ r → r < q →
        ArithmeticCurveModuleInjectiveVanishing.{u} r := by
      intro r hr hrq
      exact ih r hrq (by omega)
    have hranks : ∀ d, ArithmeticPointedCurveModuleEffacement.{u} q d :=
      arithmeticPointedCurveModuleEffacement_of_lower_degrees q hq2 hlower
    intro R S hR hS hRS hfinR hfinS X Y p hp a b H n hn hunit I hI
    exact higherDirectImage_arithmetic_curve_injective_isZero_of_rank_effacement
      q hranks R S p a b H n hn hunit I

end AlgebraicGeometry.Scheme.EtaleCohomology
