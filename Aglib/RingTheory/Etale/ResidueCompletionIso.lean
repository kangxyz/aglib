/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ResiduePowerIso
public import Aglib.RingTheory.AdicCompletion.FiniteTypeLocalComparison

/-! # Original completion of a formally etale residue neighbourhood

Every original power quotient is identified by the original scalar map.
Their actual transition equations construct the completion equivalence.
Neither a Noetherian hypothesis nor a supplied completion comparison is used.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyEtale

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [FormallyEtale R S] (I : Ideal R) (g : S →ₐ[R] R ⧸ I)

/-- The original scalar map is bijective even at the zeroth, zero-ring quotient. -/
theorem residuePowerMap_bijective (n : ℕ) : Function.Bijective (residuePowerMap I g n) := by
  by_cases hn : n = 0
  · subst n
    let : Subsingleton (R ⧸ I ^ 0) := by simp
    let : Subsingleton (S ⧸ (RingHom.ker g.toRingHom) ^ 0) := by simp
    exact Function.bijective_of_subsingleton' _
  · exact (residuePowerEquiv I g n (Nat.pos_of_ne_zero hn)).bijective

/-- One original scalar equivalence at every order, including order zero. -/
def residuePowerRingEquiv (n : ℕ) :
    (R ⧸ I ^ n) ≃+* (S ⧸ (RingHom.ker g.toRingHom) ^ n) :=
  RingEquiv.ofBijective (residuePowerMap I g n).toRingHom (residuePowerMap_bijective I g n)

theorem residuePowerRingEquiv_mk (n : ℕ) (r : R) :
    residuePowerRingEquiv I g n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((RingHom.ker g.toRingHom) ^ n) (algebraMap R S r) := rfl

/-- The original quotient transition maps commute with their scalar equivalences. -/
theorem residuePowerRingEquiv_factor {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow (RingHom.ker g.toRingHom) h (residuePowerRingEquiv I g n x) =
      residuePowerRingEquiv I g m (Ideal.Quotient.factorPow I h x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The actual source and augmentation completions, with their native scalar map. -/
def residueCompletionRingEquiv :
    AdicCompletion I R ≃+* AdicCompletion (RingHom.ker g.toRingHom) S :=
  AdicCompletion.completionOfQuotientsEquiv I (RingHom.ker g.toRingHom)
    (residuePowerRingEquiv I g) (residuePowerRingEquiv_factor I g)

/-- The completion comparison retains the original scalar inclusion on every element. -/
theorem residueCompletionRingEquiv_algebraMap (r : R) :
    residueCompletionRingEquiv I g (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion (RingHom.ker g.toRingHom) S) (algebraMap R S r) :=
  AdicCompletion.completionOfQuotientsEquiv_algebraMap I (RingHom.ker g.toRingHom)
    (residuePowerRingEquiv I g) (residuePowerRingEquiv_factor I g)
    (algebraMap R S) (residuePowerRingEquiv_mk I g) r

/-- The same original completion comparison as a base-algebra equivalence. -/
def residueCompletionAlgEquiv :
    AdicCompletion I R ≃ₐ[R] AdicCompletion (RingHom.ker g.toRingHom) S :=
  { residueCompletionRingEquiv I g with
    commutes' r := by
      change residueCompletionRingEquiv I g (algebraMap R (AdicCompletion I R) r) = _
      exact (residueCompletionRingEquiv_algebraMap I g r).trans
        (IsScalarTower.algebraMap_apply R S _ r).symm }

end Algebra.FormallyEtale
