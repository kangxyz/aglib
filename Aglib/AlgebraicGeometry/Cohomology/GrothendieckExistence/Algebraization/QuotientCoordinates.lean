/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.ScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Original quotient coordinates as canonical algebra base change

The target retains its given ring and its given scalar action before quotienting.
The quotient scalar map is the unique factor of that original scalar map. The
algebra equivalence is canonical base change of the specified original map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Algebra

universe u v w
variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A complete original quotient-algebra comparison, including its canonical
quotient scalar map and the original unit-tensor formula. -/
structure QuotientAlgebraCoordinates (I : Ideal R) (f : A →ₐ[R] B) where
  /-- The actual scalar map from the quotient coefficient ring to the target algebra. -/
  scalar : (R ⧸ I) →+* B
  factor : scalar.comp (Ideal.Quotient.mk I) = algebraMap R B
  /-- The algebra equivalence after extension along the original quotient scalar map. -/
  equiv : letI := scalar.toAlgebra
    (R ⧸ I) ⊗[R] A ≃ₐ[R ⧸ I] B
  one_tmul : letI := scalar.toAlgebra
    ∀ a : A, equiv (1 ⊗ₜ[R] a) = f a

/-- Upgrade whole original linear quotient coordinates without changing the
multiplication of either algebra. All scalar and unit equations are retained. -/
def quotientAlgebraCoordinates (I : Ideal R) (f : A →ₐ[R] B)
    (p : { e : (A ⧸ (I • (⊤ : Submodule R A))) ≃ₗ[R] B //
      ∀ a, e (Submodule.Quotient.mk a) = f a }) :
    QuotientAlgebraCoordinates I f := by
  have hkill : ∀ r ∈ I, algebraMap R B r = 0 := by
    intro r hr
    have hzero : (Submodule.Quotient.mk (r • (1 : A)) :
        A ⧸ (I • (⊤ : Submodule R A))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr trivial)
    calc
      algebraMap R B r = f (r • (1 : A)) := by simp [Algebra.smul_def]
      _ = p.val (Submodule.Quotient.mk (r • (1 : A))) := (p.property _).symm
      _ = 0 := by rw [hzero, map_zero]
  let scalar : (R ⧸ I) →+* B := Ideal.Quotient.lift I (algebraMap R B) hkill
  have hfactor : scalar.comp (Ideal.Quotient.mk I) = algebraMap R B := by
    ext r
    exact Ideal.Quotient.lift_mk I (algebraMap R B) hkill
  letI := scalar.toAlgebra
  let : IsScalarTower R (R ⧸ I) B :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⧸ I) (A := B) hfactor.symm
  let eR := (TensorProduct.quotTensorEquivQuotSMul A I).trans p.val
  let eS : (R ⧸ I) ⊗[R] A ≃ₗ[R ⧸ I] B :=
    { eR.toAddEquiv with
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        change eR (algebraMap R (R ⧸ I) r • x) =
          algebraMap R (R ⧸ I) r • eR x
        rw [IsScalarTower.algebraMap_smul, map_smul, IsScalarTower.algebraMap_smul] }
  have heS : ∀ a : A, eS (1 ⊗ₜ[R] a) = f a := by
    intro a
    change p.val (TensorProduct.quotTensorEquivQuotSMul A I (1 ⊗ₜ[R] a)) = f a
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, p.property]
  exact ⟨scalar, hfactor, baseChangeAlgEquiv f eS heS,
    baseChangeAlgEquiv_one_tmul f eS heS⟩

end AlgebraicGeometry.Scheme.Modules.Algebra
