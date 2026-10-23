/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Tsen.Basic
public import Aglib.FieldTheory.Tsen.HomogeneousZeros

/-!
# Homogeneous common zeros and the C₁ condition

Positive-degree homogeneous equations vanish at the origin. The geometric
common-zero theorem therefore applies to finite systems of such equations.
-/

@[expose] public section

namespace MvPolynomial

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem IsHomogeneous.eval_origin {K σ : Type*} [Field K]
    {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsHomogeneous d) (hd : 0 < d) :
    eval 0 p = 0 := by
  simpa [Nat.ne_of_gt hd] using hp.eval₂_mul (RingHom.id K) (0 : σ → K) (0 : K)

/-- An indexed homogeneous system with fewer equations than variables has a
nonzero common zero over an algebraically closed field. -/
theorem exists_ne_zero_common_zero_homogeneous {K ι : Type*} [Field K] [IsAlgClosed K]
    [Fintype ι] {n : ℕ} (p : ι → MvPolynomial (Fin n) K) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hcard : Fintype.card ι < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i, eval x (p i) = 0 := by
  classical
  obtain ⟨x, hx, hpx⟩ := exists_ne_zero_common_zero (Finset.univ.image p)
    (by simpa using fun i => (hp i).eval_origin (hd i))
    ((Finset.card_image_le.trans_eq (Finset.card_univ)).trans_lt hcard)
  exact ⟨x, hx, fun i => hpx _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

end MvPolynomial

namespace Field

/-- Algebraically closed fields satisfy the C₁ condition. -/
theorem isC1_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] : IsC1 K := by
  intro n d p hd hdn hp
  obtain ⟨x, hx, hpx⟩ := MvPolynomial.exists_ne_zero_common_zero {p}
    (by simpa using hp.eval_origin hd)
    (by simpa using (Nat.succ_le_iff.mpr hd).trans_lt hdn)
  exact ⟨x, hx, hpx p (Finset.mem_singleton_self p)⟩

end Field
