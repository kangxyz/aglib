/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# The canonical residue marking of a local completion

The native first-order projection from the completion is the inverse residue
marking. Exact first-order precision of algebra homomorphisms therefore gives
the literal commutative square with the original two residue quotient maps.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AdicCompletion

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The actual map of residue fields carries the original first completion
projection to the actual residue quotient of the completion. -/
theorem residueField_map_evalOneₐ (x : AdicCompletion (maximalIdeal R) R) :
    ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
      (evalOneₐ (maximalIdeal R) x) =
        residue (AdicCompletion (maximalIdeal R) R) x := by
  obtain ⟨r, hr⟩ := residue_surjective (evalOneₐ (maximalIdeal R) x)
  have hmem : algebraMap R (AdicCompletion (maximalIdeal R) R) r - x ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    rw [maximalIdeal_eq_map, ← ker_evalOneₐ_eq_map _ (maximalIdeal R).fg_of_isNoetherianRing]
    change evalOneₐ (maximalIdeal R)
      (algebraMap R (AdicCompletion (maximalIdeal R) R) r - x) = 0
    rw [map_sub, (evalOneₐ (maximalIdeal R)).commutes]
    exact sub_eq_zero.mpr hr
  rw [← hr, ResidueField.map_residue]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (residue_eq_zero_iff _).mpr hmem

/-- Ring-homomorphism form of the original completion/residue square. -/
theorem residueField_map_comp_evalOneₐ :
    (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comp
      (evalOneₐ (maximalIdeal R)).toRingHom =
        residue (AdicCompletion (maximalIdeal R) R) := by
  ext x
  exact residueField_map_evalOneₐ R x

omit [IsNoetherianRing R] in
/-- Exact precision modulo the first maximal-ideal power gives equality after
the native first projection, with no identification of different quotient types. -/
theorem evalOneₐ_comp_eq_of_precision {C : Type v} [CommRing C] [Algebra R C]
    (a : C →ₐ[R] R) (b : C →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (h : (Ideal.Quotient.mkₐ R (maximalIdeal R ^ 1)).comp a =
      (evalₐ (maximalIdeal R) 1).comp b) :
    (Ideal.Quotient.mkₐ R (maximalIdeal R)).comp a =
      (evalOneₐ (maximalIdeal R)).comp b := by
  ext c
  have hc := congrArg (Ideal.Quotient.factor
    (show maximalIdeal R ^ 1 ≤ maximalIdeal R by simp)) (AlgHom.congr_fun h c)
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.factor_mk, factorₐ_evalₐ_one] using hc

/-- The exact approximation equation gives the literal residue square for the
two original algebra homomorphisms. -/
theorem residueField_map_comp_eq_of_precision {C : Type v} [CommRing C] [Algebra R C]
    (a : C →ₐ[R] R) (b : C →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (h : (Ideal.Quotient.mkₐ R (maximalIdeal R ^ 1)).comp a =
      (evalₐ (maximalIdeal R) 1).comp b) :
    (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comp
      ((residue R).comp a.toRingHom) =
        (residue (AdicCompletion (maximalIdeal R) R)).comp b.toRingHom := by
  ext c
  have hc := AlgHom.congr_fun (evalOneₐ_comp_eq_of_precision R a b h) c
  change residue R (a c) = evalOneₐ (maximalIdeal R) (b c) at hc
  change ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
    (residue R (a c)) = residue (AdicCompletion (maximalIdeal R) R) (b c)
  rw [hc]
  exact residueField_map_evalOneₐ R (b c)

end AdicCompletion
