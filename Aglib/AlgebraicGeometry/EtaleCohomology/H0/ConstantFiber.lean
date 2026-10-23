/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFiber

/-! # Cardinality of the original finite constant geometric fibre

The actual coefficient representation and the literal trivial-cover fibre
identify the underlying finite set of a constant coefficient's geometric fibre
with its original value. No compatibility with a chosen additive marking is
required for cardinality or nontriviality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u

variable (A : Type u) [AddCommGroup A] [Finite A]
  {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- An underlying-set equivalence from the original constant coefficient's
actual geometric fibre to its original finite additive value. -/
def coefficientFiberEquiv : coefficientFiber s (coefficient A X) ≃ A :=
  ((representation A X).fiberPointEquiv s).toEquiv.trans
    ((show MarkedCoefficients.PointModule s (representation A X).group ≃
        Scheme.FiniteEtale.Fiber s (Scheme.FiniteEtale.trivialCover X A) from
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans
      (Scheme.FiniteEtale.trivialCoverFiberEquiv A s).symm)

/-- The cardinality refers to the actual geometric point's coefficient fibre. -/
theorem card_coefficientFiber :
    Nat.card (coefficientFiber s (coefficient A X)) = Nat.card A :=
  Nat.card_congr (coefficientFiberEquiv A s)

/-- A nontrivial finite constant value has a nontrivial original geometric fibre. -/
theorem nontrivial_coefficientFiber [Nontrivial A] :
    Nontrivial (coefficientFiber s (coefficient A X)) :=
  (coefficientFiberEquiv A s).nontrivial_congr.mpr inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
