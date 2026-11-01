/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Aglib.RingTheory.KrullDimension.IntegralExtension
public import Aglib.RingTheory.KrullDimension.Polynomial

/-!
# Maximal heights in a finite-type domain over a field

One actual Noether normalization supplies a faithful integral extension of
a polynomial ring. Its normality gives going down, so maximal heights
agree with those of the polynomial base. All maximal ideals therefore
have the same height, and the native supremum formula identifies it with
the intrinsic Krull dimension of the original ring.

The normalization and its number of variables are chosen only inside the
proof. No dimension-preservation family or field perfection is assumed.
-/

@[expose] public noncomputable section

universe u v

namespace Ideal

/-- Every maximal ideal of a finite-type domain over a field has height
equal to the original ring's Krull dimension, including dimension zero. -/
theorem height_eq_ringKrullDim_of_finiteType_field
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsMaximal] :
    (p.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hg, hint⟩ := _root_.exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral B A := ⟨hint⟩
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  have hheight (q : Ideal A) [q.IsMaximal] : q.height = (n : ℕ∞) := by
    let : (q.under B).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) q
    rw [Ideal.height_eq_height_under_of_normal (R := B) q]
    simpa only [Nat.card_fin] using
      MvPolynomial.mvPolynomial_height_eq_card_of_isMaximal k (Fin n) (q.under B)
  have hupper : (⨆ (q : Ideal A) (_ : q.IsMaximal), q.height) ≤ (n : ℕ∞) := by
    refine iSup_le fun q => iSup_le fun hq => ?_
    let := hq
    exact (hheight q).le
  have hlower : (n : ℕ∞) ≤ ⨆ (q : Ideal A) (_ : q.IsMaximal), q.height := by
    rw [← hheight p]
    exact le_iSup_of_le p (le_iSup_of_le (inferInstance : p.IsMaximal) le_rfl)
  have hdim := Ideal.sup_isMaximal_height_eq_ringKrullDim (R := A)
  rw [le_antisymm hupper hlower] at hdim
  simpa only [hheight p] using hdim

end Ideal
