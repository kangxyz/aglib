/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Removing localization-away torsion

The kernel of the localization map consists of power-torsion elements.
-/

@[expose] public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Localization away from `p` kills exactly the elements annihilated by a power of `p`. -/
theorem mem_ker_localizationAway_iff (p x : R) :
    x ∈ RingHom.ker (algebraMap R (Localization.Away p)) ↔ ∃ n : ℕ, p ^ n * x = 0 := by
  change algebraMap R (Localization.Away p) x = 0 ↔ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers p) (Localization.Away p)]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) p).mp s.property
    exact ⟨n, by simpa only [hn] using hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨p ^ n, ⟨n, rfl⟩⟩, hn⟩

/-- Maps sending `p` to a regular element kill the kernel of localization away from `p`. -/
theorem ker_localizationAway_le_ker (f : R →+* S) (p : R)
    (hp : IsRegular (f p)) :
    RingHom.ker (algebraMap R (Localization.Away p)) ≤ RingHom.ker f := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_ker_localizationAway_iff p x).mp hx
  change f x = 0
  apply (hp.pow n).left
  simpa only [map_mul, map_pow, map_zero, mul_zero] using congrArg f hn

/-- Removing `p`-power torsion preserves a map to any target in which the image
of `p` is regular. This is not a localization of the target. -/
def liftAwayTorsion (f : R →+* S) (p : R) (hp : IsRegular (f p)) :
    R ⧸ RingHom.ker (algebraMap R (Localization.Away p)) →+* S :=
  Ideal.Quotient.lift (RingHom.ker (algebraMap R (Localization.Away p))) f (fun _x hx =>
    ker_localizationAway_le_ker f p hp hx)

/-- The descended map agrees with the original map on quotient representatives. -/
@[simp] theorem liftAwayTorsion_mk (f : R →+* S) (p : R)
    (hp : IsRegular (f p)) (x : R) :
    liftAwayTorsion f p hp
      (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.Away p))) x) = f x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The descended map factors the original map through the actual quotient map. -/
@[simp] theorem liftAwayTorsion_comp_mk (f : R →+* S) (p : R)
    (hp : IsRegular (f p)) :
    (liftAwayTorsion f p hp).comp
      (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.Away p)))) = f := by
  ext x
  exact liftAwayTorsion_mk f p hp x

/-- The image of `p` becomes regular after quotienting by precisely the
kernel of localization away from `p`. The quotient embeds in that localization. -/
theorem isRegular_mk_ker_localizationAway (p : R) :
    IsRegular (Ideal.Quotient.mk
      (RingHom.ker (algebraMap R (Localization.Away p))) p) := by
  let f : R →+* Localization.Away p := algebraMap R (Localization.Away p)
  have hp : IsUnit (f p) :=
    IsLocalization.map_units (Localization.Away p) ⟨p, Submonoid.mem_powers p⟩
  have hl : IsLeftRegular (Ideal.Quotient.mk (RingHom.ker f) p) := by
    intro x y h
    apply RingHom.kerLift_injective f
    apply hp.isRegular.left
    simpa only [map_mul, RingHom.kerLift_mk] using congrArg (RingHom.kerLift f) h
  exact ⟨hl, fun x y h => hl (by simpa only [mul_comm] using h)⟩

/-- A map out of the torsion-free quotient is determined by its restriction
along the actual quotient map. -/
theorem liftAwayTorsion_unique (f : R →+* S) (p : R) (hp : IsRegular (f p))
    (g : R ⧸ RingHom.ker (algebraMap R (Localization.Away p)) →+* S)
    (hg : g.comp (Ideal.Quotient.mk
      (RingHom.ker (algebraMap R (Localization.Away p)))) = f) :
    g = liftAwayTorsion f p hp := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (DFunLike.congr_fun hg r).trans (liftAwayTorsion_mk f p hp r).symm

end RingHom
