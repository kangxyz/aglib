/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois

/-!
# Base-field roots and their Galois fixedness

The canonical base-field inclusion maps actual roots into the algebraic closure.
Its image is fixed by the genuine absolute Galois action.
-/

@[expose] public section

noncomputable section
namespace Field.absoluteGaloisGroup.RootsOfUnity
open Field.absoluteGaloisGroup.RootsOfUnity
variable (K : Type*) [Field K] (n : ℕ)
local notation "G" => Field.absoluteGaloisGroup K

/-- Inclusion of an actual base-field root into the roots in the algebraic closure. -/
def baseRoot (ζ : rootsOfUnity n K) : Mu K n :=
  Additive.ofMul (restrictRootsOfUnity (algebraMap K (AlgebraicClosure K)) n ζ)

@[simp] theorem baseRoot_one : baseRoot K n 1 = 0 := by
  simp [baseRoot]

/-- Multiplication of roots becomes addition in the actual additive coefficient. -/
theorem baseRoot_mul (ζ ξ : rootsOfUnity n K) :
    baseRoot K n (ζ * ξ) = baseRoot K n ζ + baseRoot K n ξ := by
  exact (restrictRootsOfUnity (algebraMap K (AlgebraicClosure K)) n).map_mul ζ ξ

/-- A base-field root is invariant under the genuine absolute Galois action. -/
@[simp] theorem baseRoot_fixed (ζ : rootsOfUnity n K) (g : G) :
    g • baseRoot K n ζ = baseRoot K n ζ := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g).commutes
    ((ζ : Kˣ) : K)

end Field.absoluteGaloisGroup.RootsOfUnity
