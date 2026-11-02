/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Canonical internal grading of an external direct sum

The homogeneous submodules are the ranges of the original linear
inclusions. Their equivalences use the original coordinate projections,
and their decomposition is the native direct sum of those equivalences.
The native externally graded ring and algebra structures supply the
internal grading on the same direct sum.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace DirectSum

variable {ι R : Type*} [DecidableEq ι] [CommRing R]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The original homogeneous linear inclusion. -/
abbrev homogeneousInclusion (i : ι) : M i →ₗ[R] ⨁ j, M j := lof R ι M i

/-- The original homogeneous linear coordinate projection. -/
abbrev homogeneousComponent (i : ι) : (⨁ j, M j) →ₗ[R] M i := DFinsupp.lapply i

@[simp]
theorem homogeneousComponent_inclusion (i : ι) (x : M i) :
    homogeneousComponent (R := R) M i (homogeneousInclusion (R := R) M i x) = x := by
  exact DirectSum.of_eq_same i x

/-- The original homogeneous inclusion as a submodule of the direct sum. -/
def summandSubmodule (i : ι) : Submodule R (⨁ j, M j) :=
  LinearMap.range (lof R ι M i)

/-- The original homogeneous inclusion and coordinate projection form
the canonical equivalence with its range. -/
def summandLinearEquiv (i : ι) : M i ≃ₗ[R] summandSubmodule (R := R) M i :=
  LinearEquiv.ofLeftInverse (f := lof R ι M i) (g := fun x => x i)
    (fun x => DirectSum.of_eq_same i x)

@[simp]
theorem summandLinearEquiv_apply (i : ι) (x : M i) :
    (summandLinearEquiv (R := R) M i x : ⨁ j, M j) = lof R ι M i x := rfl

@[simp]
theorem summandLinearEquiv_symm_apply (i : ι) (x : summandSubmodule (R := R) M i) :
    (summandLinearEquiv (R := R) M i).symm x = (x : ⨁ j, M j) i := rfl

/-- The canonical decomposition into the ranges of the original
inclusions, with no new chosen inverse. -/
def decomposeIntoSummands :
    (⨁ i, M i) ≃ₗ[R] ⨁ i, summandSubmodule (R := R) M i :=
  congrLinearEquiv (summandLinearEquiv (R := R) M)

/-- Recomposition of the original components is the identity. -/
theorem coeLinearMap_decomposeIntoSummands :
    coeLinearMap (summandSubmodule (R := R) M) ∘ₗ
      (decomposeIntoSummands (R := R) M).toLinearMap = LinearMap.id := by
  ext i x
  simp [decomposeIntoSummands, congrLinearEquiv_toLinearMap]

/-- The original component maps supply the native decomposition class. -/
@[instance_reducible]
def summandDecomposition : DirectSum.Decomposition (summandSubmodule (R := R) M) := by
  have hr : (decomposeIntoSummands (R := R) M).toLinearMap ∘ₗ
      coeLinearMap (summandSubmodule (R := R) M) = LinearMap.id := by
    apply LinearMap.ext
    intro a
    apply (decomposeIntoSummands (R := R) M).symm.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
    have h := LinearMap.congr_fun (coeLinearMap_decomposeIntoSummands (R := R) M)
      ((decomposeIntoSummands (R := R) M).symm a)
    simpa using h
  exact DirectSum.Decomposition.ofLinearMap
    (summandSubmodule (R := R) M)
    (decomposeIntoSummands (R := R) M).toLinearMap
    (coeLinearMap_decomposeIntoSummands (R := R) M) hr

variable [AddMonoid ι] [DirectSum.GRing M]

/-- Native multiplication of the original homogeneous inclusions. -/
theorem homogeneousInclusion_mul {i j : ι} (x : M i) (y : M j) :
    homogeneousInclusion (R := R) M i x * homogeneousInclusion (R := R) M j y =
      homogeneousInclusion (R := R) M (i + j) (GradedMonoid.GMul.mul x y) :=
  DirectSum.of_mul_of x y

/-- Scalar bilinearity of the original homogeneous multiplication
supplies the native graded-algebra structure. The scalar map is the
original scalar multiple of the original graded unit. -/
@[instance_reducible]
def gAlgebraOfBilinear
    (hleft : ∀ {i j} (r : R) (x : M i) (y : M j),
      GradedMonoid.GMul.mul (r • x) y = r • GradedMonoid.GMul.mul x y)
    (hright : ∀ {i j} (r : R) (x : M i) (y : M j),
      GradedMonoid.GMul.mul x (r • y) = r • GradedMonoid.GMul.mul x y) :
    DirectSum.GAlgebra R M := by
  letI : IsScalarTower R (GradedMonoid M) (GradedMonoid M) := {
    smul_assoc r x y := Sigma.ext rfl (heq_of_eq (hleft r x.2 y.2)) }
  letI : SMulCommClass R (GradedMonoid M) (GradedMonoid M) := {
    smul_comm r x y := Sigma.ext rfl (heq_of_eq (hright r x.2 y.2).symm) }
  refine {
    toFun := (LinearMap.toSpanSingleton R (M 0) GradedMonoid.GOne.one).toAddMonoidHom
    map_one := one_smul R _
    map_mul := ?_
    commutes := ?_
    smul_def := ?_ }
  · intro r s
    change (r * s) • (1 : GradedMonoid M) = (r • 1) * (s • 1)
    rw [smul_mul_assoc, one_mul, mul_smul]
  · intro r x
    change (r • (1 : GradedMonoid M)) * x = x * (r • 1)
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · intro r x
    change r • x = (r • (1 : GradedMonoid M)) * x
    rw [smul_mul_assoc, one_mul]

variable [DirectSum.GAlgebra R M]

/-- The native external graded algebra has its canonical internal
grading on the same direct-sum carrier. -/
instance summandGradedAlgebra : GradedAlgebra (summandSubmodule (R := R) M) where
  toDecomposition := summandDecomposition (R := R) M
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨GradedMonoid.GMul.mul x y, (DirectSum.of_mul_of x y).symm⟩

/-- The internal projection is the original coordinate followed by its
original linear inclusion. -/
theorem proj_summandSubmodule (i : ι) (x : ⨁ j, M j) :
    GradedAlgebra.proj (summandSubmodule (R := R) M) i x = lof R ι M i (x i) := rfl

end DirectSum
