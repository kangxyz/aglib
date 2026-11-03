/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Original local parameter data under a commuting equivalence square

The original ring maps, maximal ideals and residue maps are retained. This
single transport is shared by actual marked continuation and triple entry.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

namespace IsLocalRing

/-- An actual commuting ring-equivalence square preserves the original
parameter, minimality, centre ideal and structural residue-map bijectivity. -/
theorem parameter_properties_of_equiv_comp
    {A : Type u} {R : Type v} {S : Type w}
    [CommRing A] [CommRing R] [CommRing S]
    [IsLocalRing A] [IsLocalRing R] [IsLocalRing S]
    (f : A →+* R) (c : A →+* S) [IsLocalHom f] [IsLocalHom c]
    (e : R ≃+* S) (he : e.toRingHom.comp f = c) (t : A) (p : R)
    (hep : e.toRingHom p = c t)
    (hmin : c t ∉ maximalIdeal S ^ 2)
    (hcenter : (maximalIdeal A).map c = Ideal.span {c t})
    (hres : Function.Bijective (ResidueField.map c)) :
    p = f t ∧ p ∉ maximalIdeal R ^ 2 ∧
      (maximalIdeal A).map f = Ideal.span {p} ∧
      Function.Bijective (ResidueField.map f) := by
  have hp : p = f t := e.injective (hep.trans (RingHom.congr_fun he t).symm)
  have heinv : e.symm.toRingHom.comp c = f := by
    ext a
    apply e.injective
    exact (e.apply_symm_apply (c a)).trans (RingHom.congr_fun he a).symm
  refine ⟨hp, ?_, ?_, ?_⟩
  · intro hp2
    have h := Ideal.mem_map_of_mem e.toRingHom hp2
    have hm : (maximalIdeal R).map e.toRingHom = maximalIdeal S := by
      have hnative :=
        map_maximalIdeal_of_surjective (R := R) (S := S) e.toRingHom e.surjective
      exact hnative
    rw [Ideal.map_pow, hm, hep] at h
    exact hmin h
  · have h := congrArg (Ideal.map e.symm.toRingHom) hcenter
    rw [Ideal.map_map, heinv, Ideal.map_span, Set.image_singleton] at h
    have ht : e.symm.toRingHom (c t) = f t := RingHom.congr_fun heinv t
    rw [ht] at h
    rw [hp]
    exact h
  · let : IsLocalHom e.symm.toRingHom :=
      IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective
    have hb : Function.Bijective (ResidueField.map (e.symm.toRingHom.comp c)) := by
      rw [ResidueField.map_comp]
      change Function.Bijective
        ((ResidueField.mapEquiv (R := S) (S := R) e.symm) ∘ ResidueField.map c)
      exact (ResidueField.mapEquiv (R := S) (S := R) e.symm).bijective.comp hres
    simpa only [heinv] using hb

end IsLocalRing
