/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.LocalPoints
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Local rigidity of solutions of an etale presentation

A solution of the actual defining relations gives an algebra homomorphism by
native descent along the presentation's surjective evaluation map. If its
generator values agree with a fixed point modulo the target maximal ideal,
etale uniqueness identifies the two points exactly. This fixes coefficients
when a finitely presented etale stage is encoded by auxiliary polynomial variables.
-/

@[expose] public section

noncomputable section

open MvPolynomial IsLocalRing

namespace Algebra.Presentation

variable {R B T ν ρ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing T] [Algebra R T] [IsLocalRing T] [Algebra.Etale R B]

/-- A solution of an etale presentation with the same residue coordinates as
 a fixed point has exactly the same coordinates as that point. -/
theorem eq_point_of_relation_eq_zero_of_sub_mem_maximalIdeal
    (P : Presentation R B ν ρ) (f : B →ₐ[R] T) (z : ν → T)
    (hrel : ∀ j, aeval z (P.relation j) = 0)
    (hclose : ∀ i, z i - f (P.val i) ∈ maximalIdeal T) :
    ∀ i, z i = f (P.val i) := by
  have hker : RingHom.ker (aeval (R := R) P.val).toRingHom ≤
      RingHom.ker (aeval (R := R) z).toRingHom := by
    change RingHom.ker (aeval (R := R) P.val) ≤ RingHom.ker (aeval (R := R) z)
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hrel j
  let h : B →ₐ[R] T :=
    AlgHom.liftOfSurjective (aeval (R := R) P.val) P.aeval_val_surjective (aeval (R := R) z) hker
  have hz (i : ν) : h (P.val i) = z i := by
    simpa only [aeval_X] using
      AlgHom.liftOfSurjective_apply (aeval (R := R) P.val) P.aeval_val_surjective
        (aeval (R := R) z) hker (X i)
  let res : T →ₐ[R] ResidueField T :=
    (Algebra.ofId T (ResidueField T)).restrictScalars R
  have hpoly : (res.comp h).comp (aeval (R := R) P.val) =
      (res.comp f).comp (aeval (R := R) P.val) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    rw [hz]
    apply sub_eq_zero.mp
    rw [← map_sub]
    change IsLocalRing.residue T (z i - f (P.val i)) = 0
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hclose i)
  have hres : res.comp h = res.comp f := by
    apply AlgHom.ext
    intro b
    obtain ⟨p, rfl⟩ := P.aeval_val_surjective b
    exact AlgHom.congr_fun hpoly p
  have heq : h = f := Algebra.Etale.residue_comp_injective R T B hres
  intro i
  exact (hz i).symm.trans (AlgHom.congr_fun heq (P.val i))

end Algebra.Presentation
