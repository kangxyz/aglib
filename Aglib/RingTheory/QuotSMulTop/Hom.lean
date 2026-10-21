/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Hom out of a scalar quotient

Precomposition with the actual quotient map identifies linear maps over the
quotient ring with linear maps into a module over that ring. Naturality retains
the original maps for the degree-one change-of-rings cokernel comparison.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace QuotSMulTop

variable {R : Type*} [CommRing R] (a : R)
    (M : Type*) [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N]
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]

local instance : SMulCommClass (R ⧸ Ideal.span {a}) R N :=
  IsScalarTower.to_smulCommClass'

/-- Restrict scalars and precompose with the actual scalar quotient map. -/
def homPrecomp : (QuotSMulTop a M →ₗ[R ⧸ Ideal.span {a}] N) →ₗ[R] (M →ₗ[R] N) where
  toFun f := (f.restrictScalars R).comp (Submodule.mkQ (a • (⊤ : Submodule R M)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The universal Hom property of the scalar quotient, as a linear equivalence. -/
def homLinearEquiv : (QuotSMulTop a M →ₗ[R ⧸ Ideal.span {a}] N) ≃ₗ[R] (M →ₗ[R] N) :=
  LinearEquiv.ofBijective (homPrecomp a M N) (by
    constructor
    · intro f g h
      apply DFunLike.ext
      intro x
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (a • (⊤ : Submodule R M)) x
      exact LinearMap.congr_fun h m
    · intro f
      have ha : ∀ n : N, a • n = 0 := by
        intro n
        rw [← IsScalarTower.algebraMap_smul (R ⧸ Ideal.span {a}) a n]
        have hz : algebraMap R (R ⧸ Ideal.span {a}) a = 0 := by
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        rw [hz, zero_smul]
      have hk : a • (⊤ : Submodule R M) ≤ LinearMap.ker f := by
        intro m hm
        obtain ⟨x, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
        simp only [LinearMap.mem_ker, map_smul, ha]
      let g := (Submodule.liftQ (a • (⊤ : Submodule R M)) f hk).extendScalarsOfSurjective
        (S := R ⧸ Ideal.span {a}) Ideal.Quotient.mk_surjective
      exact ⟨g, by apply DFunLike.ext; intro m; rfl⟩)

@[simp]
theorem homLinearEquiv_apply (f : QuotSMulTop a M →ₗ[R ⧸ Ideal.span {a}] N) (m : M) :
    homLinearEquiv a M N f m = f (Submodule.Quotient.mk m) := rfl

end QuotSMulTop
