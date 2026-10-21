/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Polynomial centres with algebraically independent residues

The residue-field algebra is induced by the displayed local coefficient map.
No finiteness, domain, or discrete valuation assumption is needed.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace MvPolynomial

variable {R S ι : Type*} [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)]

/-- Algebraically independent residual coordinates have exactly the extended
maximal ideal as their centre in the polynomial ring. -/
theorem comap_maximalIdeal_aeval_of_residue_algebraicIndependent
    (z : ι → S)
    (hz : AlgebraicIndependent (ResidueField R) (fun i => residue S (z i))) :
    (maximalIdeal S).comap (aeval z).toRingHom =
      Ideal.map (C : R →+* MvPolynomial ι R) (maximalIdeal R) := by
  have he : (residue S).comp (aeval z).toRingHom =
      (aeval (fun i => residue S (z i))).toRingHom.comp (map (residue R)) := by
    apply ringHom_ext
    · intro r
      change residue S (aeval z (C r)) =
        aeval (fun i => residue S (z i)) (map (residue R) (C r))
      rw [map_C, aeval_C, aeval_C, ResidueField.algebraMap_residue]
    · intro i
      change residue S (aeval z (X i)) =
        aeval (fun i => residue S (z i)) (map (residue R) (X i))
      rw [map_X, aeval_X, aeval_X]
  calc
    (maximalIdeal S).comap (aeval z).toRingHom =
        RingHom.ker ((residue S).comp (aeval z).toRingHom) := by
      ext f
      change (aeval z f ∈ maximalIdeal S) ↔ residue S (aeval z f) = 0
      exact (residue_eq_zero_iff _).symm
    _ = RingHom.ker (map (residue R) :
        MvPolynomial ι R →+* MvPolynomial ι (ResidueField R)) := by
      rw [he, RingHom.ker_comp_of_injective _ hz]
    _ = Ideal.map (C : R →+* MvPolynomial ι R) (maximalIdeal R) := by
      rw [ker_map, ker_residue]

/-- A principal maximal ideal remains the exact polynomial centre when the
chosen coordinate residues are algebraically independent. -/
theorem comap_maximalIdeal_aeval_eq_span_C
    (p : R) (hp : maximalIdeal R = Ideal.span {p}) (z : ι → S)
    (hz : AlgebraicIndependent (ResidueField R) (fun i => residue S (z i))) :
    (maximalIdeal S).comap (aeval z).toRingHom = Ideal.span {C p} := by
  rw [comap_maximalIdeal_aeval_of_residue_algebraicIndependent z hz, hp,
    Ideal.map_span, Set.image_singleton]

end MvPolynomial
