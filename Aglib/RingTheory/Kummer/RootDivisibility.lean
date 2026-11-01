/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel

/-! # Divisibility maps between the literal root algebras

Divisibility of exponents gives the canonical map between the original
polynomial quotients, without positivity or invertibility hypotheses. An actual
root chart transports this map to the original ring. Its generic-fibre map uses
the original tensor product and a specified field containing the target; when
the generic fibre is a field it is an embedding. No splitting of the ramified
tensor ring is asserted.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace Algebra.Kummer

universe u v w z

variable {R : Type u} [CommRing R]

/-- The canonical map for divisible exponents, including level zero. -/
def rootDivisibilityHom (e N : ℕ) (h : e ∣ N) (π : R) :
    RootAlgebra e π →ₐ[R] RootAlgebra N π :=
  AdjoinRoot.liftAlgHom (rootPolynomial e π) (Algebra.ofId R (RootAlgebra N π))
    (AdjoinRoot.root (rootPolynomial N π) ^ (N / e)) (by
      simp only [rootPolynomial, Algebra.toRingHom_ofId, eval₂_sub, eval₂_pow,
        eval₂_X, eval₂_C]
      rw [← pow_mul, Nat.div_mul_cancel h, root_pow, sub_self])

@[simp] theorem rootDivisibilityHom_root (e N : ℕ) (h : e ∣ N) (π : R) :
    rootDivisibilityHom e N h π (AdjoinRoot.root (rootPolynomial e π)) =
      AdjoinRoot.root (rootPolynomial N π) ^ (N / e) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem rootDivisibilityHom_algebraMap (e N : ℕ) (h : e ∣ N)
    (π r : R) :
    rootDivisibilityHom e N h π (algebraMap R (RootAlgebra e π) r) =
      algebraMap R (RootAlgebra N π) r :=
  (rootDivisibilityHom e N h π).commutes r

section Chart

variable {S : Type v} [CommRing S] [Algebra R S]
  {e N : ℕ} {π : R}

/-- Transport the canonical divisibility map through the actual root chart. -/
def chartRootHom (E : RootAlgebra e π ≃ₐ[R] S) (h : e ∣ N) :
    S →ₐ[R] RootAlgebra N π :=
  (rootDivisibilityHom e N h π).comp E.symm.toAlgHom

@[simp] theorem chartRootHom_root (E : RootAlgebra e π ≃ₐ[R] S) (h : e ∣ N) :
    chartRootHom E h (E (AdjoinRoot.root (rootPolynomial e π))) =
      AdjoinRoot.root (rootPolynomial N π) ^ (N / e) := by
  simp [chartRootHom]

theorem chartRootHom_algebraMap (E : RootAlgebra e π ≃ₐ[R] S)
    (h : e ∣ N) (r : R) :
    chartRootHom E h (algebraMap R S r) = algebraMap R (RootAlgebra N π) r :=
  (chartRootHom E h).commutes r

variable (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
  (F : Type z) [Field F] [Algebra R F]
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [FaithfulSMul R F]

/-- Extend the actual coefficient embedding to the specified fraction field of
`R`. This is the coefficient map used by the generic chart, not a new model. -/
def rootChartCoefficientHom : K →ₐ[R] F :=
  IsFractionRing.liftAlgHom (g := Algebra.ofId R F)
    (FaithfulSMul.algebraMap_injective R F)

theorem rootChartCoefficientHom_algebraMap (r : R) :
    rootChartCoefficientHom (R := R) K F (algebraMap R K r) = algebraMap R F r :=
  (rootChartCoefficientHom (R := R) K F).commutes r

/-- The actual generic chart map on the literal tensor product. In particular,
`F` may be the fraction field of the same `RootAlgebra N π`. -/
def rootChartGenericHom (E : RootAlgebra e π ≃ₐ[R] S) (h : e ∣ N) :
    K ⊗[R] S →ₐ[R] F :=
  Algebra.TensorProduct.lift (rootChartCoefficientHom (R := R) K F)
    ((IsScalarTower.toAlgHom R (RootAlgebra N π) F).comp (chartRootHom E h))
    (fun _ _ => .all _ _)

@[simp] theorem rootChartGenericHom_tmul (E : RootAlgebra e π ≃ₐ[R] S)
    (h : e ∣ N) (k : K) (s : S) :
    rootChartGenericHom K F E h (k ⊗ₜ[R] s) =
      rootChartCoefficientHom (R := R) K F k *
        algebraMap (RootAlgebra N π) F (chartRootHom E h s) := rfl

theorem rootChartGenericHom_includeRight (E : RootAlgebra e π ≃ₐ[R] S)
    (h : e ∣ N) (s : S) :
    rootChartGenericHom K F E h (1 ⊗ₜ[R] s) =
      algebraMap (RootAlgebra N π) F (chartRootHom E h s) := by
  rw [rootChartGenericHom_tmul, map_one, one_mul]

theorem rootChartGenericHom_includeLeft (E : RootAlgebra e π ≃ₐ[R] S)
    (h : e ∣ N) (k : K) :
    rootChartGenericHom K F E h (k ⊗ₜ[R] (1 : S)) =
      rootChartCoefficientHom (R := R) K F k := by
  rw [rootChartGenericHom_tmul, map_one, map_one, mul_one]

/-- If the original generic fibre is a field, its constructed chart map is an
embedding into the specified target field. -/
theorem rootChartGenericHom_injective
    (E : RootAlgebra e π ≃ₐ[R] S) (h : e ∣ N) (hL : IsField (K ⊗[R] S)) :
    Function.Injective (rootChartGenericHom K F E h) := by
  let := hL.toField
  exact (rootChartGenericHom K F E h).injective

end Chart

end Algebra.Kummer
