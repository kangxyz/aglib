/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GenericFreeness.RegularElement
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Regular.Basic

/-! # Density of original principal opens in generic field fibres

A regular element has dense basic open in the actual prime spectrum, without
a reducedness hypothesis. Generic regularity of an original nonzero element
then gives density in every original field tensor algebra over one nonzero
principal open of the base. Empty fibres are included, not replaced by a
nonemptiness assumption.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace PrimeSpectrum

/-- The basic open of a left-regular element is dense in the original prime
spectrum. This also applies to nonreduced rings and to the zero ring. -/
theorem dense_basicOpen_of_isLeftRegular {R : Type*} [CommSemiring R]
    (b : R) (hb : IsLeftRegular b) : Dense (basicOpen b : Set (PrimeSpectrum R)) := by
  apply isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro U ⟨s, rfl⟩ ⟨p, hp⟩
  by_contra h
  have hbot : basicOpen (b * s) = ⊥ := by
    apply le_antisymm _ bot_le
    intro q hq
    have hqs : q ∈ basicOpen b ⊓ basicOpen s := by
      rwa [← basicOpen_mul]
    exact h ⟨q, hqs.2, hqs.1⟩
  obtain ⟨n, hn⟩ := (basicOpen_eq_bot_iff (b * s)).mp hbot
  have hs : s ^ n = 0 := (IsLeftRegular.pow n hb) (by
    change b ^ n * s ^ n = b ^ n * 0
    rw [mul_zero, ← mul_pow]
    exact hn)
  have hsb : basicOpen s = ⊥ := (basicOpen_eq_bot_iff s).mpr ⟨n, hs⟩
  have hpbot : p ∈ (⊥ : TopologicalSpace.Opens (PrimeSpectrum R)) := hsb ▸ hp
  exact hpbot

/-- A single nonzero base scalar makes the original principal open dense in
all original field fibres. No injectivity of `R → B` or fibre nonemptiness is
assumed. This is the affine principal-open density step, not a density theorem
for an arbitrary open of an arbitrary scheme. -/
theorem exists_ne_zero_forall_dense_basicOpen_one_tmul
    (R B : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type*) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 →
        Dense (basicOpen ((1 : L) ⊗ₜ[R] b) : Set (PrimeSpectrum (L ⊗[R] B))) := by
  obtain ⟨r, hr, h⟩ := Algebra.exists_ne_zero_forall_injective_mul_one_tmul R B b hb
  exact ⟨r, hr, fun L _ _ hL => dense_basicOpen_of_isLeftRegular _ (h L hL)⟩

end PrimeSpectrum
