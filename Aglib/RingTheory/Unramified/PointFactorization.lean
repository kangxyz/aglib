/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Unramified.Field

/-! # Finite separable factorization of a prescribed field-valued point

An essentially finite-type formally unramified algebra over a field is finite.
The kernel of the prescribed point is maximal, and its actual quotient is a
finite separable field. The quotient lift preserves the original point map;
no replacement geometric point or Galois closure is selected.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyUnramified

universe k a w

/-- A prescribed field-valued point factors through its actual finite separable
residue quotient. Essential finite type is retained explicitly. -/
theorem exists_finite_separable_factorization
    (K : Type k) [Field K] {A : Type a} [CommRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [Algebra.FormallyUnramified K A]
    {Ω : Type w} [Field Ω] [Algebra K Ω] (b : A →ₐ[K] Ω) :
    ∃ (L : Type a) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧
        ∃ (q : A →ₐ[K] L) (e : L →ₐ[K] Ω), e.comp q = b := by
  let : Module.Finite K A := finite_of_free K A
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let m := RingHom.ker b.toRingHom
  let : m.IsPrime := RingHom.ker_isPrime b.toRingHom
  let : m.IsMaximal := IsArtinianRing.isMaximal_of_isPrime m
  let L := A ⧸ m
  let : Field L := Ideal.Quotient.field m
  let : Module.Finite K L := finite_of_free K L
  let : Algebra.IsSeparable K L := isSeparable K L
  let e : L →ₐ[K] Ω := Ideal.Quotient.liftₐ m b (fun _ h => h)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    Ideal.Quotient.mkₐ K m, e, Ideal.Quotient.liftₐ_comp m b _⟩

end Algebra.FormallyUnramified
