/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Uniform powers of ideal sheaves

On a Noetherian scheme, containment of supports in the reverse direction
implies containment of a positive power of the original ideal sheaf.
The exponent is made uniform on a finite affine cover; it is not supplied
as an additional hypothesis. A pullback version retains the power on the
original base, together with its unchanged support.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- On a Noetherian scheme, a radical containment admits one positive power
bound over the entire scheme, including all its affine charts. -/
theorem exists_pos_pow_le_of_le_radical [IsNoetherian X]
    (I J : X.IdealSheafData) (h : I ≤ J.radical) :
    ∃ n : ℕ, 0 < n ∧ I ^ n ≤ J := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.affineOpens := fun i ↦
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hlocal (i : 𝒰.I₀) : ∃ n : ℕ, I.ideal (U i) ^ n ≤ J.ideal (U i) := by
    let : IsNoetherianRing Γ(X, (U i).1) :=
      IsLocallyNoetherian.component_noetherian (U i)
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h (U i))
      (I.ideal (U i)).fg_of_isNoetherianRing
  choose n hn using hlocal
  let N : ℕ := Finset.univ.sup n + 1
  refine ⟨N, Nat.succ_pos _, le_of_iSup_eq_top U 𝒰.iSup_opensRange ?_⟩
  intro i
  change I.ideal (U i) ^ N ≤ J.ideal (U i)
  have hi : n i ≤ N :=
    (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  exact (Ideal.pow_le_pow_right hi).trans (hn i)

/-- The support inclusion is reversed: `V(J) ⊆ V(I)` implies that some
positive power of `I` is contained in `J`. No reducedness assumption is needed. -/
theorem exists_pos_pow_le_of_support_le [IsNoetherian X]
    (I J : X.IdealSheafData) (h : J.support ≤ I.support) :
    ∃ n : ℕ, 0 < n ∧ I ^ n ≤ J := by
  apply exists_pos_pow_le_of_le_radical I J
  simpa only [vanishingIdeal_support] using le_support_iff_le_vanishingIdeal.mp h

/-- A supported thickening after pullback can be obtained by a power of the
original base ideal. Its support on the base is unchanged. Only the source
of the morphism needs to be Noetherian. -/
theorem exists_pos_pow_comap_le_of_support_le [IsNoetherian Y]
    (f : Y ⟶ X) (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (h : J.support ≤ (I.comap f).support) :
    ∃ n : ℕ, 0 < n ∧ (I ^ n).comap f ≤ J ∧ (I ^ n).support = I.support := by
  obtain ⟨n, hn, hle⟩ := exists_pos_pow_le_of_support_le (I.comap f) J h
  refine ⟨n, hn, ?_, I.support_pow n (Nat.ne_of_gt hn)⟩
  simpa only [comap_pow] using hle

end AlgebraicGeometry.Scheme.IdealSheafData
