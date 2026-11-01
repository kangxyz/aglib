/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Original power quotients of a formally etale residue neighbourhood

For a formally etale algebra and an original residue-valued algebra map,
the base-ideal and augmentation-kernel power quotients are isomorphic through
the original scalar map. Formal lifting and its uniqueness construct both
inverse identities; no chosen quotient comparison is an input.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyEtale

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (g : S →ₐ[R] R ⧸ I)

/-- The original base ideal maps into the original augmentation kernel. -/
theorem ideal_map_le_residueKer : I.map (algebraMap R S) ≤ RingHom.ker g.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change g (algebraMap R S r) = 0
  rw [g.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- The original scalar homomorphism on power quotients. -/
def residuePowerMap (n : ℕ) : R ⧸ I ^ n →ₐ[R] S ⧸ (RingHom.ker g.toRingHom) ^ n :=
  Ideal.quotientMapₐ (I := I ^ n) (J := (RingHom.ker g.toRingHom) ^ n)
    (Algebra.ofId R S) (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (ideal_map_le_residueKer I g) n)

/-- Native positive-order reduction onto the original base quotient. -/
def residuePowerReduction (n : ℕ) (hn : 0 < n) : R ⧸ I ^ n →ₐ[R] R ⧸ I :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')

/-- The kernel of native positive-order reduction is nilpotent. -/
theorem residuePowerReduction_ker_nilpotent (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker (residuePowerReduction I n hn).toRingHom) := by
  refine ⟨n, ?_⟩
  change (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne'))) ^ n = 0
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

variable [FormallyEtale R S]

/-- Lift the original residue map to each native positive power quotient. -/
def residuePowerLift (n : ℕ) (hn : 0 < n) : S →ₐ[R] R ⧸ I ^ n :=
  FormallySmooth.liftOfSurjective g (residuePowerReduction I n hn)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self hn.ne'))
    (residuePowerReduction_ker_nilpotent I n hn)

@[simp] theorem residuePowerReduction_lift (n : ℕ) (hn : 0 < n) (s : S) :
    residuePowerReduction I n hn (residuePowerLift I g n hn s) = g s := by
  unfold residuePowerLift
  exact FormallySmooth.liftOfSurjective_apply g (residuePowerReduction I n hn)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self hn.ne'))
    (residuePowerReduction_ker_nilpotent I n hn) s

/-- The lift kills the actual augmentation-kernel power, not a replacement ideal. -/
theorem residueKer_pow_le_ker_lift (n : ℕ) (hn : 0 < n) :
    (RingHom.ker g.toRingHom) ^ n ≤ RingHom.ker (residuePowerLift I g n hn).toRingHom := by
  have hmap : (RingHom.ker g.toRingHom).map (residuePowerLift I g n hn).toRingHom ≤
      RingHom.ker (residuePowerReduction I n hn).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    change residuePowerReduction I n hn (residuePowerLift I g n hn s) = 0
    rw [residuePowerReduction_lift]
    exact hs
  apply (Ideal.map_eq_bot_iff_le_ker (residuePowerLift I g n hn).toRingHom).mp
  apply le_bot_iff.mp
  rw [Ideal.map_pow]
  calc
    _ ≤ (RingHom.ker (residuePowerReduction I n hn).toRingHom) ^ n :=
      Ideal.pow_right_mono hmap n
    _ = ⊥ := by
      change (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne'))) ^ n = ⊥
      rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]

/-- The lifted inverse on the original augmentation-kernel power quotient. -/
def residuePowerInverse (n : ℕ) (hn : 0 < n) :
    S ⧸ (RingHom.ker g.toRingHom) ^ n →ₐ[R] R ⧸ I ^ n :=
  Ideal.Quotient.liftₐ _ (residuePowerLift I g n hn) (residueKer_pow_le_ker_lift I g n hn)

/-- The original forward scalar map is a left inverse to the constructed quotient inverse. -/
theorem residuePowerInverse_comp_map (n : ℕ) (hn : 0 < n) :
    (residuePowerInverse I g n hn).comp (residuePowerMap I g n) =
      AlgHom.id R (R ⧸ I ^ n) := by
  apply AlgHom.ext
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (residuePowerLift I g n hn).commutes r

/-- Formal unramifiedness gives the whole original right-inverse equation. -/
theorem residuePowerMap_comp_inverse (n : ℕ) (hn : 0 < n) :
    (residuePowerMap I g n).comp (residuePowerInverse I g n hn) =
      AlgHom.id R (S ⧸ (RingHom.ker g.toRingHom) ^ n) := by
  let J := RingHom.ker g.toRingHom
  let q : S ⧸ J ^ n →ₐ[R] S ⧸ J :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')
  have hq : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨n, ?_⟩
    change (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne'))) ^ n = 0
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
    rfl
  have he : q.comp ((residuePowerMap I g n).comp (residuePowerLift I g n hn)) =
      q.comp (Ideal.Quotient.mkₐ R (J ^ n)) := by
    ext s
    apply (Ideal.quotientKerAlgEquivOfSurjective
      (show Function.Surjective g from fun a => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact ⟨algebraMap R S r, g.commutes r⟩)).injective
    simp only [AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (residuePowerLift I g n hn s)
    rw [← hr]
    change g (algebraMap R S r) = g s
    rw [g.commutes]
    have hred := residuePowerReduction_lift I g n hn s
    rw [← hr] at hred
    exact hred
  have h := FormallyUnramified.lift_unique' q hq
    ((residuePowerMap I g n).comp (residuePowerLift I g n hn))
    (Ideal.Quotient.mkₐ R (J ^ n)) he
  apply AlgHom.ext
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun h s

/-- Every positive power quotient has the original scalar-map equivalence. -/
def residuePowerEquiv (n : ℕ) (hn : 0 < n) :
    (R ⧸ I ^ n) ≃ₐ[R] (S ⧸ (RingHom.ker g.toRingHom) ^ n) :=
  AlgEquiv.ofAlgHom (residuePowerMap I g n) (residuePowerInverse I g n hn)
    (residuePowerMap_comp_inverse I g n hn) (residuePowerInverse_comp_map I g n hn)

end Algebra.FormallyEtale
