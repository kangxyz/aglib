/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationLocalRing
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The extended maximal ideal of henselization

Localizing an actual etale neighborhood at the kernel of its residue point
reduces the assertion to the native maximal-ideal theorem for essentially finite
type formally unramified local algebras. No Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The maximal ideal of the constructed henselization is extended from the base. -/
theorem map_maximalIdeal :
    (maximalIdeal R).map (algebraMap R (Henselization R)) =
      maximalIdeal (Henselization R) := by
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
  intro x hx
  obtain ⟨X, a, rfl⟩ := exists_rep R x
  let q : Ideal X.algebra := RingHom.ker X.point.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime X.point.toRingHom
  let L := Localization.AtPrime q
  have hpoint (r : R) : X.point (algebraMap R X.algebra r) =
      IsLocalRing.residue R r := X.point.commutes r
  let : IsLocalHom (algebraMap R L) := by
    constructor
    intro r hr
    apply (IsLocalRing.residue_ne_zero_iff_isUnit r).mp
    have hu : IsUnit (algebraMap X.algebra L (algebraMap R X.algebra r)) := by
      simpa only [← IsScalarTower.algebraMap_apply R X.algebra L] using hr
    have hn := (IsLocalization.AtPrime.isUnit_to_map_iff L q _).mp hu
    change X.point (algebraMap R X.algebra r) ≠ 0 at hn
    rwa [hpoint] at hn
  have hm : (maximalIdeal R).map (algebraMap R L) = maximalIdeal L :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hu (s : q.primeCompl) : IsUnit (ι R X s) := by
    apply isUnit_of_residue_ne_zero R
    rw [show residue R (ι R X s) = X.point s from
      AlgHom.congr_fun (residue_comp_ι R X) s]
    exact s.property
  let p : L →ₐ[R] Henselization R :=
    IsLocalization.liftAlgHom (S := L) (f := ι R X) hu
  have hp (b : X.algebra) : p (algebraMap X.algebra L b) = ι R X b := by
    exact IsLocalization.lift_eq (S := L) (g := (ι R X).toRingHom) hu b
  have ha : a ∈ q := by
    change X.point a = 0
    have hz : residue R (ι R X a) = 0 := by
      rw [maximalIdeal_eq_ker_residue] at hx
      change (residue R).toRingHom (ι R X a) = 0 at hx
      change (residue R).toRingHom (ι R X a) = 0
      exact hx
    rwa [show residue R (ι R X a) = X.point a from
      AlgHom.congr_fun (residue_comp_ι R X) a] at hz
  have hla : algebraMap X.algebra L a ∈ maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L q a).mpr ha
  have hmem := Ideal.mem_map_of_mem p.toRingHom hla
  rw [← hm, Ideal.map_map] at hmem
  have hbase : p.toRingHom.comp (algebraMap R L) =
      algebraMap R (Henselization R) := by
    apply RingHom.ext
    intro r
    exact p.commutes r
  change p (algebraMap X.algebra L a) ∈
    (maximalIdeal R).map (p.toRingHom.comp (algebraMap R L)) at hmem
  rwa [hbase, hp] at hmem

end Henselization
