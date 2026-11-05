/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.FiniteType

/-! # Finite dimension bounds for finite-type algebras

The actual finite polynomial presentation gives a finite bound over a
Noetherian base with a supplied finite bound. In particular, arithmetic
finite-type rings have finite dimension. The zero-ring case is retained.
No finite-dimensionality conclusion is inferred from Noetherianity alone.
-/

@[expose] public noncomputable section

namespace Algebra.FiniteType

universe u v

/-- A finite-type algebra over a finite-dimensional Noetherian base has an
actual natural-number dimension bound. -/
theorem exists_ringKrullDim_le_of_base_bound
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing R] [Algebra.FiniteType R A]
    (d : ℕ) (hR : ringKrullDim R ≤ d) :
    ∃ e : ℕ, ringKrullDim A ≤ e := by
  obtain ⟨n, φ, hφ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType R A)
  refine ⟨d + n, ?_⟩
  calc
    ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) R) :=
      ringKrullDim_le_of_surjective φ.toRingHom hφ
    _ = ringKrullDim R + n := by simp
    _ ≤ (d + n : ℕ) := by
      simpa only [Nat.cast_add, add_comm] using add_le_add_right hR (n : WithBot ℕ∞)

/-- The original arithmetic ring, including the zero ring, has finite
Krull dimension through its actual integer polynomial presentation. -/
theorem exists_ringKrullDim_le_of_finiteType_int
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A] :
    ∃ d : ℕ, ringKrullDim A ≤ d :=
  exists_ringKrullDim_le_of_base_bound ℤ A 1
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ))

end Algebra.FiniteType
