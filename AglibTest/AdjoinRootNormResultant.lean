/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootNormResultant
public import Lean.Util.CollectAxioms

/-!
# Consumers of quotient-field norm and resultant reciprocity
-/

@[expose] public noncomputable section

open Polynomial

namespace AglibTest.AdjoinRootNormResultant

variable {k : Type*} [Field k] [CharZero k]

/-- The evaluated element uses the actual quotient algebra and determinant norm. -/
theorem evaluatedPolynomial (p q : k[X]) (hp : p.Monic) [Fact (Irreducible p)] :
    Algebra.norm k (aeval (AdjoinRoot.root p) q) = Polynomial.resultant p q := by
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.norm_mk_eq_resultant p q hp

/-- The signed reciprocity required when both evaluations are nonzero units. -/
theorem distinctIrreducibles (p q : k[X]) (hp : p.Monic) (hq : q.Monic)
    [Fact (Irreducible p)] [Fact (Irreducible q)] :
    Algebra.norm k (AdjoinRoot.mk p q) = (-1) ^ (p.natDegree * q.natDegree) *
      Algebra.norm k (AdjoinRoot.mk q p) :=
  AdjoinRoot.norm_mk_reciprocity p q hp hq

/-- For a linear quotient, the norm really reduces to ordinary evaluation. -/
theorem linearExtension (a : k) (q : k[X]) :
    Algebra.norm k (AdjoinRoot.mk (X - C a) q) = q.eval a := by
  let : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩
  rw [AdjoinRoot.norm_mk_eq_resultant (X - C a) q (monic_X_sub_C a)]
  simpa only [natDegree_X_sub_C] using
    resultant_X_sub_C_left q q.natDegree a le_rfl

/-- Degree one in each variable gives the negative sign, including equal roots. -/
theorem linearReciprocity (a b : k) :
    Algebra.norm k (AdjoinRoot.mk (X - C a) (X - C b)) =
      -Algebra.norm k (AdjoinRoot.mk (X - C b) (X - C a)) := by
  let : Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩
  let : Fact (Irreducible (X - C b)) := ⟨irreducible_X_sub_C b⟩
  simpa only [natDegree_X_sub_C, one_mul, pow_one, neg_one_mul] using
    AdjoinRoot.norm_mk_reciprocity (X - C a) (X - C b) (monic_X_sub_C a)
      (monic_X_sub_C b)

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.norm_mk_eq_resultant, ``AdjoinRoot.norm_mk_reciprocity,
      ``evaluatedPolynomial, ``distinctIrreducibles, ``linearExtension, ``linearReciprocity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual quotient-field norm resultant identities use only standard foundations."

end AglibTest.AdjoinRootNormResultant
