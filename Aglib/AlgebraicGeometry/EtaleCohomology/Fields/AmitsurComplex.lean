/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.AffineUnits
public import Aglib.FieldTheory.Galois.AmitsurPrimitives
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Primitives in the original alternating Amitsur unit complex

The complex is the native alternating-coface construction on the original
algebraic conerve and actual ring-unit coefficients. Its degree-two primitive
statement is a concrete consequence of the original multiplicative equations.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Simplicial
open GroupCohomology.Kummer.Coefficients
open Algebra.Amitsur

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

variable (E L : Type u) [Field E] [Field L] [Algebra E L]

/-- The original Amitsur conerve with actual unit coefficients and alternating signs. -/
def amitsurUnitComplex : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (conerve E L ⋙ forget₂ (CommAlgCat E) CommRingCat ⋙ ringUnitCoefficients)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual first differential is the usual three-face multiplicative equation. -/
theorem amitsurUnitComplex_d₁ (b : (amitsurUnitComplex E L).X 1) :
    ((amitsurUnitComplex E L).d 1 2 b).down.toMul =
      unitCoface E L 1 0 b.down.toMul / unitCoface E L 1 1 b.down.toMul *
        unitCoface E L 1 2 b.down.toMul := by
  let Q : CosimplicialObject AddCommGrpCat.{u + 1} :=
    conerve E L ⋙ forget₂ (CommAlgCat E) CommRingCat ⋙ ringUnitCoefficients
  change ((∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • Q.δ i) b).down.toMul = _
  simp [Fin.sum_univ_succ, Q, CosimplicialObject.δ, unitCoface,
    ringUnitCoefficients, div_eq_mul_inv, mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual second differential is the usual four-face multiplicative equation. -/
theorem amitsurUnitComplex_d₂ (c : (amitsurUnitComplex E L).X 2) :
    ((amitsurUnitComplex E L).d 2 3 c).down.toMul =
      unitCoface E L 2 0 c.down.toMul / unitCoface E L 2 1 c.down.toMul *
        unitCoface E L 2 2 c.down.toMul / unitCoface E L 2 3 c.down.toMul := by
  let Q : CosimplicialObject AddCommGrpCat.{u + 1} :=
    conerve E L ⋙ forget₂ (CommAlgCat E) CommRingCat ⋙ ringUnitCoefficients
  change ((∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • Q.δ i) c).down.toMul = _
  simp [Fin.sum_univ_succ, Q, CosimplicialObject.δ, unitCoface,
    ringUnitCoefficients, div_eq_mul_inv, mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual degree-two cocycle of the original alternating unit complex
has a primitive over an algebraic function field. -/
theorem amitsurUnitComplex_exists_primitive
    [FiniteDimensional E L] [IsGalois E L]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra (RatFunc K) E]
    [Algebra.IsAlgebraic (RatFunc K) E]
    (c : (amitsurUnitComplex E L).X 2)
    (hc : (amitsurUnitComplex E L).d 2 3 c = 0) :
    ∃ b : (amitsurUnitComplex E L).X 1, (amitsurUnitComplex E L).d 1 2 b = c := by
  have hc' : unitCoface E L 2 0 c.down.toMul / unitCoface E L 2 1 c.down.toMul *
      unitCoface E L 2 2 c.down.toMul / unitCoface E L 2 3 c.down.toMul = 1 := by
    rw [← amitsurUnitComplex_d₂, hc]
    rfl
  obtain ⟨b, hb⟩ := exists_unit_primitive_of_algebraic_ratFunc E L K c.down.toMul hc'
  let b' : (amitsurUnitComplex E L).X 1 := ULift.up (Additive.ofMul b)
  refine ⟨b', ULift.ext _ _ ?_⟩
  exact (amitsurUnitComplex_d₁ E L b').trans hb

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
