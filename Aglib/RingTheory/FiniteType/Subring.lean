/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.FiniteType

/-!
# Units and finite-type generated subrings


Source: `R5Lab.Aglib.RingTheory.FiniteType.Subring`.
Packet SHA-256:
`a8e83e37d3a461bf89f69c97dfc6befcd7a09a020faf33ae8cc4698fbfc3292f`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace Subring
universe u v
variable {K : Type u} [Field K]
/-- Restrict a unit using both its value and its inverse in the subring. -/
def restrictRingUnit (A : Subring K) (a : Kˣ)
    (ha : (a : K) ∈ A) (hai : ((a⁻¹ : Kˣ) : K) ∈ A) : Aˣ where
  val := ⟨a, ha⟩
  inv := ⟨((a⁻¹ : Kˣ) : K), hai⟩
  val_inv := Subtype.ext a.val_inv
  inv_val := Subtype.ext a.inv_val

@[simp] theorem map_restrictRingUnit (A : Subring K) (a : Kˣ)
    (ha : (a : K) ∈ A) (hai : ((a⁻¹ : Kˣ) : K) ∈ A) :
    Units.map A.subtype.toMonoidHom (restrictRingUnit A a ha hai) = a := by
  apply Units.ext
  rfl

/-- Closure of finite ring data is finite type over the integers. -/
theorem subringClosure_finiteType (s : Finset K) :
    Algebra.FiniteType ℤ (Subring.closure (s : Set K)) := by
  have h := Algebra.FiniteType.adjoin_of_finite (R := ℤ) s.finite_toSet
  exact h.equiv (Subring.closureEquivAdjoinInt (s : Set K)).symm

end Subring
