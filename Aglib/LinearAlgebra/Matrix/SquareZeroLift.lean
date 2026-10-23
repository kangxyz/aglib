/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.SquareZeroUnits
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Idempotents

/-!
# Lifting finite idempotent matrices across a square-zero kernel

Entrywise scalar reduction has square-zero kernel when the original ring map
does. Native idempotent lifting therefore lifts an actual finite projector.
The map in the conclusion is the original entrywise ring homomorphism.
-/

@[expose] public section

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Products of two matrices killed by a square-zero scalar reduction vanish. -/
theorem mul_eq_zero_of_map_eq_zero (f : R →+* S)
    (hf : RingHom.ker f ^ 2 = ⊥) (A B : Matrix n n R)
    (hA : f.mapMatrix A = 0) (hB : f.mapMatrix B = 0) : A * B = 0 := by
  ext i j
  change ∑ k, A i k * B k j = 0
  apply Finset.sum_eq_zero
  intro k _
  apply (RingHom.ker f).mul_eq_zero_of_mem_of_square_zero hf
  · exact congrArg (fun M : Matrix n n S => M i k) hA
  · exact congrArg (fun M : Matrix n n S => M k j) hB

/-- A surjective scalar homomorphism lifts each finite matrix entrywise. -/
theorem mapMatrix_surjective_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) :
    Function.Surjective (f.mapMatrix : Matrix n n R →+* Matrix n n S) := by
  intro A
  classical
  choose B hB using fun i j => hf (A i j)
  exact ⟨B, funext fun i => funext fun j => hB i j⟩

/-- Every finite projector lifts through the original surjective scalar map
with square-zero kernel. No local or Noetherian hypothesis is needed. -/
theorem exists_idempotent_lift_of_square_zero (f : R →+* S)
    (hsurj : Function.Surjective f) (hf : RingHom.ker f ^ 2 = ⊥)
    (p : Matrix n n S) (hp : p * p = p) :
    ∃ q : Matrix n n R, q * q = q ∧ f.mapMatrix q = p := by
  have hnil : ∀ A ∈ RingHom.ker (f.mapMatrix (m := n)), IsNilpotent A := by
    intro A hA
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact mul_eq_zero_of_map_eq_zero f hf A A hA hA
  obtain ⟨q, hq, hmap⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (f.mapMatrix (m := n)) hnil p ((mapMatrix_surjective_of_surjective f hsurj) p) hp
  exact ⟨q, hq, hmap⟩

end Matrix
