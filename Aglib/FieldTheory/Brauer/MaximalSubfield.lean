/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.ScalarExtension
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A full-degree embedded subfield splits a central division algebra

The division algebra is regarded as a right vector space over the embedded
field. Native left scalar multiplication gives its representation in linear
endomorphisms. Scalar-extension simplicity makes this representation injective;
the tower law and the full-degree hypothesis make it surjective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {K E D : Type*} [Field K] [Field E] [DivisionRing D]
  [Algebra K E] [Algebra K D]

@[instance_reducible]
private def rightSubfieldModule (j : E →ₐ[K] D) : Module E D :=
  Module.compHom D (j.toRingHom.toOpposite fun x y => by
    change j x * j y = j y * j x
    rw [← map_mul, ← map_mul, mul_comm])

/-- An embedded subfield of degree `n` splits a central division algebra of
square dimension `n²`. The embedding need not be central and no reduced norm
or pre-existing matrix splitting is required. -/
theorem nonempty_matrix_of_subfield_finrank
    [FiniteDimensional K D] [IsCentral K D]
    (j : E →ₐ[K] D) (n : ℕ) [NeZero n]
    (hD : Module.finrank K D = n ^ 2) (hE : Module.finrank K E = n) :
    Nonempty (E ⊗[K] D ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  classical
  let : Module E D := rightSubfieldModule j
  let : IsScalarTower K E D := ⟨fun k s d => by
    change d * j (k • s) = k • (d * j s)
    rw [map_smul, mul_smul_comm]⟩
  let : SMulCommClass D E D := ⟨fun a s d => by
    change a * (d * j s) = (a * d) * j s
    exact (mul_assoc _ _ _).symm⟩
  let : SMulCommClass E K D := ⟨fun s k d => by
    change (k • d) * j s = k • (d * j s)
    exact smul_mul_assoc _ _ _⟩
  let : FiniteDimensional E D := Module.Finite.of_restrictScalars_finite K E D
  let C : CSA K := { toAlgCat := AlgCat.of K D }
  let : IsSimpleRing (E ⊗[K] D) := CSA.isSimpleRing_baseChange C E
  let f : D →ₐ[K] Module.End E D := Algebra.lsmul K E D
  let g : E ⊗[K] D →ₐ[E] Module.End E D :=
    AlgHom.liftEquiv K E D (Module.End E D) f
  have hinj : Function.Injective g := g.toRingHom.injective
  have hr : Module.finrank E D = n := by
    have h := Module.finrank_mul_finrank K E D
    rw [hD, hE] at h
    exact Nat.mul_left_cancel (NeZero.pos n) (by simpa only [pow_two] using h)
  have hdim : Module.finrank E (E ⊗[K] D) = Module.finrank E (Module.End E D) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap, hD, hr, pow_two]
  have hsurj : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := g.toLinearMap)).mp hinj
  let b := (Module.finBasis E D).reindex (finCongr hr)
  exact ⟨(AlgEquiv.ofBijective g ⟨hinj, hsurj⟩).trans (LinearMap.toMatrixAlgEquiv b)⟩

end Algebra
