/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationMap
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The local henselization selected by an actual target map

A map from any commutative ring to a local ring selects the inverse image of
the target maximal ideal. Its prime localization has a canonical local map
to the target. If the target is henselian, the actual henselization has its
unique local extension, with the original coefficient and residue maps.

No finite-type, Noetherian, domain or flatness hypothesis is needed here.
-/

@[expose] public noncomputable section

universe u v

namespace Localization.AtLocalTarget

open IsLocalRing

variable {B : Type u} {R : Type v} [CommRing B] [CommRing R] [IsLocalRing R]
  (f : B →+* R)

/-- The prime selected by the actual map to a local ring. -/
abbrev prime : Ideal B := (maximalIdeal R).comap f

instance prime_isPrime : (prime f).IsPrime := Ideal.comap_isPrime f _

/-- The actual localization at the inverse image of the target maximal ideal. -/
abbrev Ring := Localization.AtPrime (prime f)

/-- The original map extends to its selected prime localization. -/
def map : Ring f →+* R :=
  IsLocalization.lift (M := (prime f).primeCompl) (g := f)
    (fun s => notMem_maximalIdeal.mp s.property)

@[simp] theorem map_algebraMap (b : B) :
    map f (algebraMap B (Ring f) b) = f b :=
  IsLocalization.lift_eq _ b

theorem map_comp_algebraMap :
    (map f).comp (algebraMap B (Ring f)) = f :=
  RingHom.ext (map_algebraMap f)

/-- The selected localization map is local even when the original map is not. -/
instance map_isLocalHom : IsLocalHom (map f) := by
  have hm : maximalIdeal (Ring f) ≤ (maximalIdeal R).comap (map f) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (prime f) (Ring f)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change map f (algebraMap B (Ring f) b) ∈ maximalIdeal R
    rwa [map_algebraMap]
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  exact (show ¬ IsUnit (map f x) from hm hn) hx

end Localization.AtLocalTarget

namespace Henselization.AtLocalTarget

open IsLocalRing

variable {B : Type u} {R : Type v} [CommRing B] [CommRing R]
  [HenselianLocalRing R] (f : B →+* R)

/-- The actual henselization of the prime localization selected by the target. -/
abbrev Ring := Henselization (Localization.AtLocalTarget.Ring f)

/-- The original coefficient map into the selected local henselization. -/
def of : B →+* Ring f :=
  (algebraMap (Localization.AtLocalTarget.Ring f) (Ring f)).comp
    (algebraMap B (Localization.AtLocalTarget.Ring f))

/-- The canonical local map from the selected henselization to the target. -/
def map : Ring f →+* R :=
  (Henselization.existsUnique_local_ringHom (Localization.AtLocalTarget.map f)).choose

instance map_isLocalHom : IsLocalHom (map f) :=
  (Henselization.existsUnique_local_ringHom
    (Localization.AtLocalTarget.map f)).choose_spec.1.1

theorem map_comp_algebraMap :
    (map f).comp (algebraMap (Localization.AtLocalTarget.Ring f) (Ring f)) =
      Localization.AtLocalTarget.map f :=
  (Henselization.existsUnique_local_ringHom
    (Localization.AtLocalTarget.map f)).choose_spec.1.2

@[simp] theorem map_of (b : B) : map f (of f b) = f b := by
  change map f (algebraMap (Localization.AtLocalTarget.Ring f) (Ring f)
    (algebraMap B (Localization.AtLocalTarget.Ring f) b)) = f b
  exact (RingHom.congr_fun (map_comp_algebraMap f)
    (algebraMap B (Localization.AtLocalTarget.Ring f) b)).trans
      (Localization.AtLocalTarget.map_algebraMap f b)

theorem map_comp_of : (map f).comp (of f) = f := RingHom.ext (map_of f)

/-- The induced map on actual residue fields retains the original coefficients. -/
@[simp] theorem residueMap_residue_of (b : B) :
    ResidueField.map (map f) (IsLocalRing.residue (Ring f) (of f b)) =
      IsLocalRing.residue R (f b) := by
  rw [ResidueField.map_residue, map_of]

end Henselization.AtLocalTarget
