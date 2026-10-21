/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Aglib.RingTheory.MvPolynomial.Triangular
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Actual triangular automorphisms of the polynomial localization

Constant-coefficient invariance preserves the origin ideal. The native
localization equivalence then gives the actual coordinate automorphism of the
local polynomial ring, with literal original polynomial compatibility.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
variable (p : Fin n) (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i)

include he

/-- The actual triangular polynomial map preserves the origin ideal. -/
theorem originIdeal_comap_triangular :
    originIdeal R n = (originIdeal R n).comap (MvPolynomial.triangularAlgEquiv R p e) := by
  ext f
  change MvPolynomial.constantCoeff f ∈ maximalIdeal R ↔
    MvPolynomial.constantCoeff (MvPolynomial.triangularAlgEquiv R p e f) ∈ maximalIdeal R
  rw [MvPolynomial.constantCoeff_triangularAlgEquiv R p e he]

/-- The native localization equivalence for the actual triangular polynomial map. -/
def triangularAlgEquiv : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n :=
  Localization.localAlgEquiv (originIdeal R n) (originIdeal R n)
    (MvPolynomial.triangularAlgEquiv R p e) (originIdeal_comap_triangular R n p e he)

/-- Forward coordinate change commutes with the original polynomial localization map. -/
theorem triangularAlgEquiv_algebraMap (f : MvPolynomial (Fin n) R) :
    triangularAlgEquiv R n p e he
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) f) =
      algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n)
        (MvPolynomial.triangularAlgEquiv R p e f) :=
  Localization.localRingHom_to_map (originIdeal R n) (originIdeal R n)
    (MvPolynomial.triangularAlgEquiv R p e).toRingHom
      (originIdeal_comap_triangular R n p e he) f

/-- Inverse coordinate change commutes with the original polynomial localization map. -/
theorem triangularAlgEquiv_symm_algebraMap (f : MvPolynomial (Fin n) R) :
    (triangularAlgEquiv R n p e he).symm
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) f) =
      algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n)
        ((MvPolynomial.triangularAlgEquiv R p e).symm f) := by
  apply (triangularAlgEquiv R n p e he).injective
  rw [AlgEquiv.apply_symm_apply, triangularAlgEquiv_algebraMap, AlgEquiv.apply_symm_apply]

/-- The actual local coordinate automorphism preserves every maximal-ideal power. -/
theorem triangularAlgEquiv_mem_maximalIdeal_pow_iff (c : ℕ) (x : PolynomialLocalRing R n) :
    triangularAlgEquiv R n p e he x ∈ maximalIdeal (PolynomialLocalRing R n) ^ c ↔
      x ∈ maximalIdeal (PolynomialLocalRing R n) ^ c := by
  have hm : (maximalIdeal (PolynomialLocalRing R n) ^ c).map
      (triangularAlgEquiv R n p e he).toRingEquiv = maximalIdeal (PolynomialLocalRing R n) ^ c := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have h := Ideal.apply_mem_of_equiv_iff
    (I := maximalIdeal (PolynomialLocalRing R n) ^ c)
    (f := (triangularAlgEquiv R n p e he).toRingEquiv) (x := x)
  rw [hm] at h
  exact h

end PolynomialLocalRing
