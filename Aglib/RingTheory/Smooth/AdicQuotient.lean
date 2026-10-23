/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Formal smoothness of actual adic quotients

For a flat ring map, formal smoothness of its reduction modulo an ideal
implies formal smoothness of its reductions modulo every positive power.
The maps are the literal quotient maps, and the induction uses the actual
transition maps between the quotients. No Noetherian or finiteness
assumption is imposed.
-/

@[expose] public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The actual quotient map of a flat ring map is flat by base change. -/
theorem Flat.quotientMap {f : R →+* S} (hf : f.Flat) (I : Ideal R) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by
  algebraize [f]
  change (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).Flat
  rw [flat_algebraMap_iff]
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv

/-- A flat map whose reduction modulo `I` is formally smooth has formally
smooth reductions modulo all positive powers of `I`. -/
theorem FormallySmooth.quotientMap_pow_of_flat {f : R →+* S} (hf : f.Flat)
    (I : Ideal R)
    (hI : (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FormallySmooth)
    (n : ℕ) (hn : 0 < n) :
    (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map).FormallySmooth := by
  induction n, hn using Nat.le_induction with
  | base =>
    change (Ideal.quotientMap ((I ^ 1).map f) f Ideal.le_comap_map).FormallySmooth
    rw [pow_one]
    exact hI
  | succ n hn ih =>
    let fnext : R ⧸ I ^ (n + 1) →+* S ⧸ (I ^ (n + 1)).map f :=
      Ideal.quotientMap ((I ^ (n + 1)).map f) f Ideal.le_comap_map
    let fprev : R ⧸ I ^ n →+* S ⧸ (I ^ n).map f :=
      Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map
    let qR : R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ)
    let qS : S ⧸ (I ^ (n + 1)).map f →+* S ⧸ (I ^ n).map f :=
      Ideal.Quotient.factor (Ideal.map_mono (Ideal.pow_le_pow_right n.le_succ))
    apply FormallySmooth.of_flat_of_ker_eq_map_of_square_zero fnext
      (hf.quotientMap (I ^ (n + 1))) qR qS fprev
      (Ideal.Quotient.factor_surjective _) (Ideal.Quotient.factor_surjective _)
    · apply Ideal.Quotient.ringHom_ext
      ext x
      rfl
    · dsimp only [qR]
      rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
      exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
    · dsimp only [qR, qS, fnext]
      rw [Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker,
        Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
    · exact ih

end RingHom
