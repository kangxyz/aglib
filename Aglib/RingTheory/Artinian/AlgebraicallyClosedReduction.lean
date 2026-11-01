/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! # Split reduction of a finite algebra over an algebraically closed field

The original Artinian nilradical quotient is the product of the original
maximal quotients. Each maximal quotient is a finite integral field extension
of the algebraically closed base, so its actual structural map is invertible.
Composing these maps gives an original algebra surjection onto the product
of copies of the base indexed by the original maximal spectrum. Its kernel
is exactly the original nilradical and has a positive nilpotence exponent.

The coefficient and algebra universes are independent. No reducedness or
nontriviality of the finite algebra is assumed; the zero algebra has empty
maximal spectrum. This is a field-level split-thickening construction, not
finite-stage descent or a spreading theorem over a general base ring.
-/

@[expose] public noncomputable section

namespace Algebra.FiniteAlgebra

universe u v

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (A : Type v) [CommRing A] [Algebra Ω A] [Module.Finite Ω A]

/-- The inverse of the actual scalar map identifies an original maximal
quotient of the finite algebra with the algebraically closed base field. -/
def residueBaseEquiv (m : MaximalSpectrum A) : (A ⧸ m.asIdeal) ≃ₐ[Ω] Ω := by
  have : m.asIdeal.IsMaximal := m.isMaximal
  let : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact (AlgEquiv.ofBijective (Algebra.ofId Ω (A ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

/-- The actual nilradical quotient is the product over the original maximal
spectrum, without choosing a numerical reindexing or a new algebra model. -/
def reductionEquivPi : (A ⧸ nilradical A) ≃ₐ[Ω] (MaximalSpectrum A → Ω) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  exact ((IsArtinianRing.quotNilradicalEquivPi A).restrictScalars Ω).trans
    (AlgEquiv.piCongrRight (residueBaseEquiv Ω A))

/-- The original quotient map followed by the actual scalar identifications
is the split-reduction algebra homomorphism. -/
def splitReductionMap : A →ₐ[Ω] (MaximalSpectrum A → Ω) :=
  (reductionEquivPi Ω A).toAlgHom.comp (Ideal.Quotient.mkₐ Ω (nilradical A))

/-- Every coordinate is the original maximal-ideal quotient followed by the
inverse of its original scalar map. -/
@[simp] theorem splitReductionMap_apply (a : A) (m : MaximalSpectrum A) :
    splitReductionMap Ω A a m = residueBaseEquiv Ω A m (Ideal.Quotient.mk m.asIdeal a) := rfl

/-- The split-reduction map is genuinely surjective, including the zero algebra. -/
theorem splitReductionMap_surjective : Function.Surjective (splitReductionMap Ω A) :=
  (reductionEquivPi Ω A).surjective.comp Ideal.Quotient.mk_surjective

/-- Its kernel is the original nilradical, not merely an unspecified nil ideal. -/
theorem ker_splitReductionMap :
    RingHom.ker (splitReductionMap Ω A).toRingHom = nilradical A := by
  ext a
  change reductionEquivPi Ω A (Ideal.Quotient.mk (nilradical A) a) = 0 ↔
    a ∈ nilradical A
  constructor
  · intro ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (reductionEquivPi Ω A).injective
    exact ha.trans (map_zero (reductionEquivPi Ω A)).symm
  · intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The actual kernel is nilpotent by the original Artinian nilradical theorem. -/
theorem isNilpotent_ker_splitReductionMap :
    IsNilpotent (RingHom.ker (splitReductionMap Ω A).toRingHom) := by
  rw [ker_splitReductionMap]
  let : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  exact IsArtinianRing.isNilpotent_nilradical

/-- A positive exponent kills the original kernel; positivity also covers
an empty maximal spectrum and the zero algebra without an exception. -/
theorem exists_positive_pow_ker_splitReductionMap_eq_bot :
    ∃ n : ℕ, 0 < n ∧ (RingHom.ker (splitReductionMap Ω A).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := isNilpotent_ker_splitReductionMap Ω A
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]

end Algebra.FiniteAlgebra
