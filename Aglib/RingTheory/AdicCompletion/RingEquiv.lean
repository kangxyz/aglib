/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Native adic completions under a ring equivalence

The comparison is constructed from the actual finite quotient equivalences, with
independent source and target universes. It preserves every finite projection and
the extended powers of the original ideal.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (e : R ≃+* S) (I : Ideal R)

/-- The actual equivalence at each finite ideal-power quotient. -/
def quotientPowEquiv (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ (I.map (e : R →+* S)) ^ n :=
  Ideal.quotientEquiv _ _ e (Ideal.map_pow (e : R →+* S) I n).symm

@[simp] theorem quotientPowEquiv_mk (n : ℕ) (r : R) :
    quotientPowEquiv e I n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (e : R →+* S)) ^ n) (e r) := rfl

@[simp] theorem quotientPowEquiv_symm_mk (n : ℕ) (s : S) :
    (quotientPowEquiv e I n).symm
      (Ideal.Quotient.mk ((I.map (e : R →+* S)) ^ n) s) =
        Ideal.Quotient.mk (I ^ n) (e.symm s) := rfl

/-- The actual quotient equivalences commute with the transition maps. -/
theorem factor_quotientPowEquiv {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (quotientPowEquiv e I n x) =
      quotientPowEquiv e I m (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The inverse finite quotient equivalences commute with transitions too. -/
theorem factor_quotientPowEquiv_symm {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (I.map (e : R →+* S)) ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) ((quotientPowEquiv e I n).symm x) =
      (quotientPowEquiv e I m).symm
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The forward native completion map. -/
def ringEquivMap : AdicCompletion I R →+* AdicCompletion (I.map (e : R →+* S)) S :=
  liftRingHom (I.map (e : R →+* S))
    (fun n => (quotientPowEquiv e I n).toRingHom.comp (evalₐ I n).toRingHom)
    (fun {m n} h => by
      ext x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
        (quotientPowEquiv e I n (evalₐ I n x)) =
          quotientPowEquiv e I m (evalₐ I m x)
      rw [factor_quotientPowEquiv e I h, factor_evalₐ I h])

/-- The inverse native completion map uses the inverse finite quotient maps. -/
def ringEquivMapInv : AdicCompletion (I.map (e : R →+* S)) S →+* AdicCompletion I R :=
  liftRingHom I
    (fun n => (quotientPowEquiv e I n).symm.toRingHom.comp
      (evalₐ (I.map (e : R →+* S)) n).toRingHom)
    (fun {m n} h => by
      ext x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
        ((quotientPowEquiv e I n).symm (evalₐ (I.map (e : R →+* S)) n x)) =
          (quotientPowEquiv e I m).symm (evalₐ (I.map (e : R →+* S)) m x)
      rw [factor_quotientPowEquiv_symm e I h, factor_evalₐ (I.map (e : R →+* S)) h])

@[simp] theorem evalₐ_ringEquivMap (n : ℕ) (x : AdicCompletion I R) :
    evalₐ (I.map (e : R →+* S)) n (ringEquivMap e I x) =
      quotientPowEquiv e I n (evalₐ I n x) := by
  exact evalₐ_liftRingHom _ _ _ n x

@[simp] theorem evalₐ_ringEquivMapInv (n : ℕ)
    (x : AdicCompletion (I.map (e : R →+* S)) S) :
    evalₐ I n (ringEquivMapInv e I x) =
      (quotientPowEquiv e I n).symm (evalₐ (I.map (e : R →+* S)) n x) := by
  exact evalₐ_liftRingHom _ _ _ n x

/-- The actual native adic completion equivalence associated to a ring equivalence. -/
def congrRingEquiv : AdicCompletion I R ≃+* AdicCompletion (I.map (e : R →+* S)) S :=
  { ringEquivMap e I with
    invFun := ringEquivMapInv e I
    left_inv := fun x => ext_evalₐ fun n => by
      change evalₐ I n (ringEquivMapInv e I (ringEquivMap e I x)) = _
      rw [evalₐ_ringEquivMapInv, evalₐ_ringEquivMap]
      exact (quotientPowEquiv e I n).symm_apply_apply _
    right_inv := fun x => ext_evalₐ fun n => by
      change evalₐ (I.map (e : R →+* S)) n (ringEquivMap e I (ringEquivMapInv e I x)) = _
      rw [evalₐ_ringEquivMap, evalₐ_ringEquivMapInv]
      exact (quotientPowEquiv e I n).apply_symm_apply _ }

@[simp] theorem evalₐ_congrRingEquiv (n : ℕ) (x : AdicCompletion I R) :
    evalₐ (I.map (e : R →+* S)) n (congrRingEquiv e I x) =
      quotientPowEquiv e I n (evalₐ I n x) := evalₐ_ringEquivMap e I n x

@[simp] theorem evalₐ_congrRingEquiv_symm (n : ℕ)
    (x : AdicCompletion (I.map (e : R →+* S)) S) :
    evalₐ I n ((congrRingEquiv e I).symm x) =
      (quotientPowEquiv e I n).symm (evalₐ (I.map (e : R →+* S)) n x) :=
  evalₐ_ringEquivMapInv e I n x

@[simp] theorem congrRingEquiv_algebraMap (r : R) :
    congrRingEquiv e I (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion (I.map (e : R →+* S)) S) (e r) := by
  apply ext_evalₐ
  intro n
  change evalₐ (I.map (e : R →+* S)) n (congrRingEquiv e I (of I R r)) =
    evalₐ (I.map (e : R →+* S)) n (of (I.map (e : R →+* S)) S (e r))
  simp only [evalₐ_congrRingEquiv, evalₐ_of, quotientPowEquiv_mk]

/-- Extended ideal powers are carried to the literal extended powers on the target. -/
theorem congrRingEquiv_map_power (n : ℕ) :
    ((I ^ n).map (algebraMap R (AdicCompletion I R))).map
      (congrRingEquiv e I).toRingHom =
        ((I.map (e : R →+* S)) ^ n).map
          (algebraMap S (AdicCompletion (I.map (e : R →+* S)) S)) := by
  rw [Ideal.map_map, ← Ideal.map_pow, Ideal.map_map]
  congr 1

/-- Properness of the ideal is unchanged by the original ring equivalence. -/
theorem map_ne_top_of_ringEquiv (hI : I ≠ ⊤) : I.map (e : R →+* S) ≠ ⊤ := by
  intro h
  apply hI
  apply top_unique
  intro r _
  have hr : e r ∈ I.map (e : R →+* S) := by rw [h]; trivial
  obtain ⟨a, ha, he⟩ := (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).mp hr
  exact e.injective he ▸ ha

end AdicCompletion
