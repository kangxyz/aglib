/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Completion maps constructed from the actual finite quotients -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (f : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map f = J)

/-- The finite quotient map attached to the actual ideal extension equality. -/
def idealMapQuotient (n : ℕ) : R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.Quotient.lift (I ^ n) ((Ideal.Quotient.mk (J ^ n)).comp f) fun x hx => by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h : f x ∈ (I ^ n).map f := Ideal.mem_map_of_mem f hx
    rwa [Ideal.map_pow, hIJ] at h

@[simp] theorem idealMapQuotient_mk (n : ℕ) (r : R) :
    idealMapQuotient f I J hIJ n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (J ^ n) (f r) := rfl

/-- Finite quotient maps commute with the literal reduction maps. -/
theorem factor_idealMapQuotient {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (idealMapQuotient f I J hIJ n x) =
      idealMapQuotient f I J hIJ m
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The actual completion map, without identifying either completion with another carrier. -/
def idealMap : AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J
    (fun n => (idealMapQuotient f I J hIJ n).comp (evalₐ I n).toRingHom)
    (fun {m n} h => by
      ext x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
        (idealMapQuotient f I J hIJ n (evalₐ I n x)) =
          idealMapQuotient f I J hIJ m (evalₐ I m x)
      rw [factor_idealMapQuotient f I J hIJ h, factor_evalₐ I h])

@[simp] theorem evalₐ_idealMap (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (idealMap f I J hIJ x) = idealMapQuotient f I J hIJ n (evalₐ I n x) :=
  evalₐ_liftRingHom _ _ _ n x

/-- The scalar square is an equality for the original algebra maps. -/
@[simp] theorem idealMap_algebraMap (r : R) :
    idealMap f I J hIJ (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  apply ext_evalₐ
  intro n
  change evalₐ J n (idealMap f I J hIJ (of I R r)) = evalₐ J n (of J S (f r))
  simp only [evalₐ_idealMap, evalₐ_of, idealMapQuotient_mk]

end AdicCompletion
