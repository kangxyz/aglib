/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Localization at an actual field-valued point

The native prime localization retains the original point and its residue field.
-/

@[expose] public noncomputable section

namespace Localization.ResiduePoint

open IsLocalRing

variable {A E : Type*} [CommRing A] [Field E] (f : A →+* E)

/-- The actual prime selected by the field-valued point. -/
abbrev ideal : Ideal A := RingHom.ker f

instance : (ideal f).IsPrime := RingHom.ker_isPrime f

/-- The actual prime localization, not a supplied local model. -/
abbrev Ring := Localization.AtPrime (ideal f)

/-- The original point extends to its prime localization. -/
def point : Ring f →+* E :=
  IsLocalization.lift (M := (ideal f).primeCompl)
    (g := f) (fun s => isUnit_iff_ne_zero.mpr s.property)

@[simp] theorem point_algebraMap (a : A) :
    point f (algebraMap A (Ring f) a) = f a :=
  IsLocalization.lift_eq _ a

/-- The extended point is local, because its kernel contains the actual maximal ideal. -/
instance point_isLocalHom : IsLocalHom (point f) := by
  have hker : maximalIdeal (Ring f) ≤ RingHom.ker (point f) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (ideal f) (Ring f)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change point f (algebraMap A (Ring f) a) = 0
    rw [point_algebraMap]
    exact ha
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  exact (isUnit_iff_ne_zero.mp hx) (hker hn)

/-- The actual localized point has exactly the actual maximal ideal as kernel. -/
theorem ker_point : RingHom.ker (point f) = maximalIdeal (Ring f) := by
  ext x
  change point f x = 0 ↔ ¬ IsUnit x
  constructor
  · intro hz hx
    exact (hx.map (point f)).ne_zero hz
  · intro hn
    by_contra hz
    exact hn (isUnit_of_map_unit (point f) x (isUnit_iff_ne_zero.mpr hz))

/-- A surjective original point identifies the actual localized residue field with its target. -/
def residueEquiv (hf : Function.Surjective f) : ResidueField (Ring f) ≃+* E :=
  RingEquiv.ofBijective (ResidueField.lift (point f)) ⟨RingHom.injective _, fun x => by
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨residue (Ring f) (algebraMap A (Ring f) a), point_algebraMap f a⟩⟩

@[simp] theorem residueEquiv_residue (hf : Function.Surjective f) (x : Ring f) :
    residueEquiv f hf (residue (Ring f) x) = point f x := rfl

theorem residueEquiv_algebraMap (hf : Function.Surjective f) (a : A) :
    residueEquiv f hf (residue (Ring f) (algebraMap A (Ring f) a)) = f a :=
  point_algebraMap f a

end Localization.ResiduePoint
