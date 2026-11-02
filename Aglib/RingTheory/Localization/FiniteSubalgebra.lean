/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Adjoin.FG

/-! # Finite fraction subalgebras lie in a principal localization -/

@[expose] public noncomputable section

namespace IsFractionRing

universe u v

/-- A finitely generated subalgebra of a fraction field embeds into a principal
localization of the original domain. The original inclusion into the fraction field
is the literal composite of the two displayed algebra maps. -/
theorem exists_principal_localization_of_fg_subalgebra
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K]
    (B : Subalgebra R K) (hB : B.FG) :
    ∃ s : R, s ≠ 0 ∧
      ∃ (v : Localization.Away s →ₐ[R] K) (i : B →ₐ[R] Localization.Away s),
        Function.Injective v ∧ v.comp i = B.val := by
  classical
  obtain ⟨t, ht⟩ := hB
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) t
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.property
  have hsK : algebraMap R K s ≠ 0 := by
    intro h
    apply hs0
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  let v : Localization.Away (s : R) →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom (s : R) (f := Algebra.ofId R K) (isUnit_iff_ne_zero.mpr hsK)
  have hv : Function.Injective v := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (s : R))
      v.toRingHom).mpr
    intro x y
    constructor
    · exact congrArg v
    · intro h
      apply congrArg (algebraMap R (Localization.Away (s : R)))
      apply IsFractionRing.injective R K
      change v (algebraMap R _ x) = v (algebraMap R _ y) at h
      simpa only [AlgHom.commutes] using h
  have hle : B ≤ v.range := by
    rw [← ht]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨a, ha⟩ := hs x hx
    refine ⟨algebraMap R (Localization.Away (s : R)) a *
      IsLocalization.Away.invSelf (s : R), ?_⟩
    apply mul_left_cancel₀ hsK
    calc
      algebraMap R K s * v (algebraMap R (Localization.Away (s : R)) a *
          IsLocalization.Away.invSelf (s : R)) =
          v (algebraMap R (Localization.Away (s : R)) s *
            (algebraMap R (Localization.Away (s : R)) a *
              IsLocalization.Away.invSelf (s : R))) := by simp only [map_mul, AlgHom.commutes]
      _ = v (algebraMap R (Localization.Away (s : R)) a) := by
        congr 1
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
      _ = algebraMap R K a := v.commutes a
      _ = algebraMap R K s * x := by simpa only [Algebra.smul_def] using ha
  let e := AlgEquiv.ofInjective v hv
  let i : B →ₐ[R] Localization.Away (s : R) :=
    e.symm.toAlgHom.comp (Subalgebra.inclusion hle)
  refine ⟨s, hs0, v, i, hv, ?_⟩
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply ⟨b.val, hle b.property⟩)

end IsFractionRing
