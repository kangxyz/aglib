/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Etale
public import Aglib.RingTheory.Etale.LocalPoints

/-!
# Etale points modulo proper ideals of a Henselian local ring

Every point of an etale algebra modulo a proper ideal of a Henselian local
ring lifts uniquely to that ring. The quotient need only be local, not equipped
with a Henselian instance. No nilpotence or finite-generation hypothesis on the
ideal is used. The lift preserves the actual quotient map exactly.
-/

@[expose] public section

noncomputable section
open IsLocalRing

namespace HenselianLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

/-- Points of an etale algebra modulo any proper ideal lift uniquely to the
Henselian local base ring along the original quotient map. -/
theorem quotient_comp_bijective_of_etale (B : Type*) [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (I : Ideal R) (hI : I ≠ ⊤) :
    Function.Bijective (fun g : B →ₐ[R] R => (Ideal.Quotient.mkₐ R I).comp g) := by
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : R →ₐ[R] R ⧸ I := Ideal.Quotient.mkₐ R I
  let r : R ⧸ I →ₐ[R] ResidueField R :=
    Ideal.Quotient.factorₐ R (le_maximalIdeal hI)
  have hr : Function.Surjective r := Ideal.Quotient.factor_surjective (le_maximalIdeal hI)
  have hker : RingHom.ker r.toRingHom = maximalIdeal (R ⧸ I) :=
    ker_eq_maximalIdeal r.toRingHom hr
  have hcomp (g : B →ₐ[R] R) :
      r.comp (q.comp g) = (Algebra.ofId R (ResidueField R)).comp g := by
    ext x
    exact r.commutes (g x)
  constructor
  · intro f g h
    apply (residue_comp_bijective_of_etale R B).1
    change (Algebra.ofId R (ResidueField R)).comp f =
      (Algebra.ofId R (ResidueField R)).comp g
    rw [← hcomp f, ← hcomp g]
    exact congrArg (fun k : B →ₐ[R] R ⧸ I => r.comp k) h
  · intro f
    obtain ⟨g, hg⟩ := (residue_comp_bijective_of_etale R B).2 (r.comp f)
    refine ⟨g, ?_⟩
    apply Algebra.Etale.residue_comp_injective R (R ⧸ I) B
    ext b
    change residue (R ⧸ I) (q (g b)) = residue (R ⧸ I) (f b)
    have hb : r (q (g b)) = r (f b) := by
      exact AlgHom.congr_fun ((hcomp g).trans hg) b
    have hm : q (g b) - f b ∈ maximalIdeal (R ⧸ I) := by
      rw [← hker]
      change r (q (g b) - f b) = 0
      rw [map_sub, hb, sub_self]
    have hz := (residue_eq_zero_iff (q (g b) - f b)).mpr hm
    simpa only [map_sub, sub_eq_zero] using hz

end HenselianLocalRing
