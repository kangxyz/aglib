/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.NormalDimensionStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.IntegralBoundaryReduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.NormalBoundaryReduction

/-! # Sharp torsion cohomological dimension for proper field schemes

Simultaneous induction over all algebraically closed fields uses the actual
finite normalization, proper birational codimension-two boundary, projective
line graph, and original unit-cone and Leray comparisons. Every internally
torsion coefficient on a proper scheme of dimension at most `d` has zero
original cohomology above `2 * d`, including characteristic-primary torsion.
The final Ext universe remains arbitrary.

This is the geometric-field part of Stacks, Tag 095U.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

private theorem proper_sharp_dimension_bound_standard (d : ℕ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsProper p],
      topologicalKrullDim X ≤ (d : ℕ) →
        ∀ F : AbelianSheaf.{u, u + 1} X, IsTorsion X F →
          ∀ q : ℕ, 2 * d < q → Subsingleton (Sheaf.H.{u + 2} F q) := by
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
            apply subsingleton_H_of_normal_and_boundary (d + 1) r ?_ ?_ pY hdimY G hG
            · intro Z _ pZ _ hZ hdimZ H hH
              apply subsingleton_H_of_isTorsion_of_proper_normal_dimension_step
                d (2 * (d + 1)) (2 * d) ?_ ?_ pZ hZ
                  (by simpa only [Nat.add_assoc] using hdimZ) H hH (r + 1)
                    (by omega) (by omega)
              · intro K _ _ W pW _ hdimW I hI n hn
                exact ih (d + 1) (by omega) K W pW hdimW I hI n hn
              · intro K _ _ W pW _ hdimW I hI n hn
                exact ih d (by omega) K W pW hdimW I hI n hn
            · intro Z pZ _ hdimZ H hH
              exact ih (d + 1) (by omega) k Z pZ hdimZ H hH r (by omega)
          · intro Z pZ _ hdimZ G hG
            exact ih (d + 1) (by omega) k Z pZ hdimZ G hG r (by omega)

/-- Proper schemes of dimension at most `d` over algebraically closed fields
have original torsion cohomology zero in every degree above `2 * d`.
No uniform annihilator or invertibility of the torsion is assumed. -/
theorem subsingleton_H_of_isTorsion_of_proper_dimension_le
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : ℕ))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 * d < q) : Subsingleton (Sheaf.H.{e} F q) := by
  let : Subsingleton (Sheaf.H.{u + 2} F q) :=
    proper_sharp_dimension_bound_standard d k X p hdim F hF q hq
  let E : Sheaf.H.{e} F q ≃ Sheaf.H.{u + 2} F q := Ext.chgUniv
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
