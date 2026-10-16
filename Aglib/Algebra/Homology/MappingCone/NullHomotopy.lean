/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Lifting through a cone nullhomotopy

For arbitrary cochain complexes in an abelian category, a nullhomotopy of
the composite into the original mapping cone gives an actual chain lift up
to an actual chain homotopy.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalQuasiIsoLifting.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `db71c57024ab73a5264ab112f4d0932f98e889dac4887d0b15f459cdf94137da`.
Selected declaration ranges: 40–53.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

namespace CochainComplex

theorem exists_lift_of_cone_nullHomotopy {A : Type*} [Category* A] [Abelian A]
    {P K L : CochainComplex A ℤ} (s : K ⟶ L) (f : P ⟶ L)
    (h : Homotopy (f ≫ mappingCone.inr s) 0) :
    ∃ g : P ⟶ K, Nonempty (Homotopy f (g ≫ s)) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hzero : Q.map f ≫ Q.map (mappingCone.inr s) = 0 := by
    rw [← Q.map_comp]
    exact (HomotopyCategory.eq_of_homotopy _ _ h).trans (Q.map_zero _ _)
  obtain ⟨g, hg⟩ := (mappingCone.triangleh s).coyoneda_exact₂
    (HomotopyCategory.mappingCone_triangleh_distinguished s) (Q.map f) hzero
  obtain ⟨g, rfl⟩ := Q.map_surjective g
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq f (g ≫ s) ?_⟩⟩
  change Q.map f = Q.map g ≫ Q.map s at hg
  exact hg.trans (Q.map_comp g s).symm

end CochainComplex
