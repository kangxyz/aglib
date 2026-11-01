/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.IntegralDimensionStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.IntegralBoundaryReduction

/-! # An auxiliary finite torsion cohomological bound for proper field schemes

The simultaneous induction over all algebraically closed fields uses the
actual dimension-zero and curve bounds, the rational graph dimension step,
and integral-component/boundary reduction. It gives the explicit auxiliary
bound `3 * d - 1` (natural subtraction, hence zero when `d = 0`).

The actual coefficient is internally torsion, not necessarily killed by a
single integer, and characteristic-primary torsion is included. Original Ext
change of universe retains an arbitrary final cohomology universe. This
finite bound is not the sharp theorem with bound `2 * d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

private theorem proper_dimension_bound_standard (d : ℕ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsProper p],
      topologicalKrullDim X ≤ (d : ℕ) →
        ∀ F : AbelianSheaf.{u, u + 1} X, IsTorsion X F →
          ∀ q : ℕ, 3 * d - 1 < q → Subsingleton (Sheaf.H.{u + 2} F q) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k _ _ X p _ hdim F hF q hq
    cases d with
    | zero =>
      exact subsingleton_H_of_proper_dimension_le_zero p (by simpa using hdim)
        F q (by simpa using hq)
    | succ d =>
      cases d with
      | zero =>
        exact subsingleton_H_of_isTorsion_of_proper_curve p (by simpa using hdim)
          F hF q (by simpa using hq)
      | succ d =>
        cases q with
        | zero => omega
        | succ r =>
          apply subsingleton_H_of_integral_and_boundary (d + 1) r ?_ ?_ p
            (by simpa only [Nat.succ_eq_add_one] using hdim) F hF
          · intro Y _ pY _ hdimY G hG
            apply subsingleton_H_of_isTorsion_of_proper_integral_dimension_step
              (d + 1) (3 * (d + 1) - 1) ?_ pY hdimY G hG (r + 1) (by omega)
            intro K _ _ Z pZ _ hdimZ H hH n hn
            exact ih (d + 1) (by omega) K Z pZ hdimZ H hH n hn
          · intro Z pZ _ hdimZ G hG
            exact ih (d + 1) (by omega) k Z pZ hdimZ G hG r (by omega)

/-- Proper schemes of dimension at most `d` over algebraically closed fields
have the auxiliary finite original torsion cohomological bound `3 * d - 1`.
The subtraction is natural, so the bound is zero in dimension zero and two
in dimension one. This does not assert the sharper general bound `2 * d`. -/
theorem subsingleton_H_of_isTorsion_of_proper_finite_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 3 * d - 1 < q) : Subsingleton (Sheaf.H.{e} F q) := by
  let : Subsingleton (Sheaf.H.{u + 2} F q) :=
    proper_dimension_bound_standard d k X p hdim F hF q hq
  let E : Sheaf.H.{e} F q ≃ Sheaf.H.{u + 2} F q := Ext.chgUniv
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
