/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuotSMulTop

/-! Scalar quotients commute with finite products through the original quotient maps. -/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace QuotSMulTop

variable {R : Type*} [CommRing R] (a : R) (M : Type*) [AddCommGroup M] [Module R M]
  (ι : Type*)

/-- A scalar multiple of a product is the product of the scalar multiples. -/
theorem smul_top_pi :
    a • (⊤ : Submodule R (ι → M)) =
      Submodule.pi Set.univ (fun _ : ι ↦ a • (⊤ : Submodule R M)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    apply Submodule.mem_pi.mpr
    intro i _
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y i, trivial, rfl⟩
  · intro hx
    have h (i : ι) : ∃ y : M, a • y = x i := by
      obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
        (Submodule.mem_pi.mp hx i (Set.mem_univ i))
      exact ⟨y, hy⟩
    choose y hy using h
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨y, trivial, funext hy⟩

/-- The actual quotient-product comparison, linear over the scalar quotient ring. -/
def piEquiv [Fintype ι] [DecidableEq ι] :
    QuotSMulTop a (ι → M) ≃ₗ[R ⧸ Ideal.span {a}] (ι → QuotSMulTop a M) :=
  ((Submodule.quotEquivOfEq _ _ (smul_top_pi a M ι)).trans
    (Submodule.quotientPi (fun _ : ι ↦ a • (⊤ : Submodule R M)))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

@[simp]
theorem piEquiv_mk [Fintype ι] [DecidableEq ι] (x : ι → M) :
    piEquiv a M ι (Submodule.Quotient.mk x) = fun i ↦ Submodule.Quotient.mk (x i) := rfl

end QuotSMulTop
