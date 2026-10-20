/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PointModule

/-!
# ScalarPoint for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `ScalarPoint.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c97f29ce2b6473a979ec9170450f0c6780a68b8d0e7b7f409756da51236306a6`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {K : Type u} [Field K]

/-- Laurent evaluation at (a,b), extracted from the original rank-one action. -/
def scalarEval (a b : Kˣ) : Laurent K →ₐ[K] K where
  toFun r := representation (Object.unitPair a b) r 1
  map_zero' := by simp
  map_one' := by simp
  map_add' r s := by simp
  map_mul' r s := by
    rw [map_mul]
    change representation (Object.unitPair a b) r
      (representation (Object.unitPair a b) s 1) = _
    simp
  commutes' r := by
    change representation (Object.unitPair a b) (algebraMap K (Laurent K) r) 1 = r
    rw [AlgHom.commutes]
    simp

@[simp] theorem scalarEval_first (a b : Kˣ) :
    scalarEval a b (firstCoordinate K) = (a : K) := by
  change representation (Object.unitPair a b) (firstCoordinate K) 1 = _
  rw [representation_first]
  change (a : K) * 1 = _
  exact mul_one _

@[simp] theorem scalarEval_second (a b : Kˣ) :
    scalarEval a b (secondCoordinate K) = (b : K) := by
  change representation (Object.unitPair a b) (secondCoordinate K) 1 = _
  rw [representation_second]
  change (b : K) * 1 = _
  exact mul_one _

theorem scalarEval_surjective (a b : Kˣ) : Function.Surjective (scalarEval a b) := by
  intro c
  exact ⟨algebraMap K (Laurent K) c, (scalarEval a b).commutes c⟩

/-- The literal prime ideal ker(eval_(a,b)) is finite and dominant. -/
def scalarPoint (a b : Kˣ) : FiniteDominantPrime K := by
  let p : Ideal (Laurent K) := RingHom.ker (scalarEval a b)
  have hp : p.IsPrime := RingHom.ker_isPrime (scalarEval a b)
  have hf : Module.Finite K (Laurent K ⧸ p) :=
    Module.Finite.of_injective (Ideal.kerLiftAlg (scalarEval a b)).toLinearMap
      (Ideal.kerLiftAlg_injective (scalarEval a b))
  refine ⟨p, hp, hf, ?_⟩
  ext c
  change scalarEval a b (algebraMap K (Laurent K) c) = 0 ↔ c = 0
  rw [(scalarEval a b).commutes]
  rfl

/-- The actual residue algebra at the scalar point is canonically K. -/
def scalarResidueEquiv (a b : Kˣ) : PointAlgebra (scalarPoint a b) ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (scalarEval_surjective a b)

@[simp] theorem scalarResidueEquiv_mk (a b : Kˣ) (r : Laurent K) :
    scalarResidueEquiv a b (Ideal.Quotient.mk (scalarPoint a b).val r) =
      scalarEval a b r :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The point-object construction and the ORIGINAL scalar pair are intertwined
by the literal evaluation residue isomorphism in the stated coordinate order. -/
def scalarPointObjectIso (a b : Kˣ) :
    Object.Iso (pointObject (scalarPoint a b)) (Object.unitPair a b) where
  linearEquiv := (scalarResidueEquiv a b).toLinearEquiv
  commute_a x := by
    change PointAlgebra (scalarPoint a b) at x
    change scalarResidueEquiv a b
      (Ideal.Quotient.mk (scalarPoint a b).val (firstCoordinate K) * x) =
      (a : K) * scalarResidueEquiv a b x
    rw [map_mul, scalarResidueEquiv_mk, scalarEval_first]
  commute_b x := by
    change PointAlgebra (scalarPoint a b) at x
    change scalarResidueEquiv a b
      (Ideal.Quotient.mk (scalarPoint a b).val (secondCoordinate K) * x) =
      (b : K) * scalarResidueEquiv a b x
    rw [map_mul, scalarResidueEquiv_mk, scalarEval_second]

/-- The full original support-length cycle is exactly the scalar point, with
positive coefficient one and zero coefficient at every different prime. -/
theorem objectCycle_unitPair (a b : Kˣ) :
    objectCycle (Object.unitPair a b) = FreeAbelianGroup.of (scalarPoint a b) :=
  (objectCycle_iso (scalarPointObjectIso a b)).symm.trans (objectCycle_pointObject _)

/-- The scalar-point reduction is exactly the two identity-coordinate axes. -/
theorem scalarPoint_onIdentityAxis_iff (a b : Kˣ) :
    OnIdentityAxis (scalarPoint a b) ↔ (a : K) = 1 ∨ (b : K) = 1 := by
  change scalarEval a b (firstCoordinate K - 1) = 0 ∨
    scalarEval a b (secondCoordinate K - 1) = 0 ↔ _
  simp only [map_sub, map_one, scalarEval_first, scalarEval_second, sub_eq_zero]

end AlgebraicGeometry.Torus.FiniteCorrespondence
