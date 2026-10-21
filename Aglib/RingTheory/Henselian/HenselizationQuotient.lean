/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationUniversal
public import Aglib.RingTheory.Henselian.HenselizationMaximalIdeal
public import Aglib.RingTheory.Henselian.QuotientMaximalIdeal

/-!
# Infinitesimal quotients of henselization

The map induced by the original base algebra structure is an isomorphism on
positive maximal-ideal power quotients. Its inverse comes from the actual
universal property, applied to the proved Henselian infinitesimal quotient.
No Noetherian or completion comparison theorem is used.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The native quotient map induced by the original base algebra structure. -/
def quotientMaximalIdealPowMap (n : ℕ) :
    R ⧸ maximalIdeal R ^ n →ₐ[R]
      Henselization R ⧸ maximalIdeal (Henselization R) ^ n :=
  Ideal.quotientMapₐ _ (Algebra.ofId R (Henselization R))
    (Ideal.map_le_iff_le_comap.mp (by
      change (maximalIdeal R ^ n).map (algebraMap R (Henselization R)) ≤ _
      rw [Ideal.map_pow, map_maximalIdeal]))

/-- Positive infinitesimal quotient maps of the actual henselization are bijective. -/
theorem quotientMaximalIdealPowMap_bijective (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (quotientMaximalIdealPowMap R n) := by
  let JR := maximalIdeal R ^ n
  let JH := maximalIdeal (Henselization R) ^ n
  let QR := R ⧸ JR
  let QH := Henselization R ⧸ JH
  let : HenselianLocalRing QR := HenselianLocalRing.quotient_maximalIdeal_pow R n hn
  let : HenselianLocalRing QH :=
    HenselianLocalRing.quotient_maximalIdeal_pow (Henselization R) n hn
  let : IsLocalHom (algebraMap R QR) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk JR) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk JH) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk JH) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R QH) := by
    change IsLocalHom ((Ideal.Quotient.mk JH).comp (algebraMap R (Henselization R)))
    infer_instance
  let F : QR →ₐ[R] QH := quotientMaximalIdealPowMap R n
  let : IsLocalHom F.toRingHom := by
    constructor
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr : IsUnit (algebraMap R QH r) := by
      change IsUnit (F (algebraMap R QR r)) at ha
      rwa [F.commutes] at ha
    exact ((isUnit_map_iff (algebraMap R QH) r).mp hr).map (Ideal.Quotient.mk JR)
  let ψ : Henselization R →ₐ[R] QR := (existsUnique_local_algHom R QR).choose
  let : IsLocalHom ψ.toRingHom := (existsUnique_local_algHom R QR).choose_spec.1
  have hkill : ∀ x : Henselization R, x ∈ JH → ψ x = 0 := by
    have hmap : JH.map ψ.toRingHom = ⊥ := by
      change (maximalIdeal (Henselization R) ^ n).map ψ.toRingHom = ⊥
      rw [← map_maximalIdeal R, ← Ideal.map_pow, Ideal.map_map]
      have he : ψ.toRingHom.comp (algebraMap R (Henselization R)) =
          Ideal.Quotient.mk JR := by
        apply RingHom.ext
        intro r
        exact ψ.commutes r
      change (maximalIdeal R ^ n).map
        (ψ.toRingHom.comp (algebraMap R (Henselization R))) = ⊥
      rw [he]
      exact Ideal.map_quotient_self JR
    intro x hx
    have h := Ideal.mem_map_of_mem ψ.toRingHom hx
    rw [hmap] at h
    exact h
  let G : QH →ₐ[R] QR := Ideal.Quotient.liftₐ JH ψ hkill
  have hGF : Function.LeftInverse G F := by
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change ψ (algebraMap R (Henselization R) r) = Ideal.Quotient.mk JR r
    exact ψ.commutes r
  let qH : Henselization R →ₐ[R] QH := Ideal.Quotient.mkₐ R JH
  have hcomp : F.comp ψ = qH := by
    let : IsLocalHom (F.comp ψ).toRingHom :=
      RingHom.isLocalHom_comp F.toRingHom ψ.toRingHom
    let : IsLocalHom qH.toRingHom := inferInstanceAs (IsLocalHom (Ideal.Quotient.mk JH))
    exact (existsUnique_local_algHom R QH).unique inferInstance inferInstance
  have hFG : Function.RightInverse G F := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact AlgHom.congr_fun hcomp x
  exact ⟨hGF.injective, hFG.surjective⟩

/-- The infinitesimal quotient equivalence with its original induced map. -/
def quotientMaximalIdealPowEquiv (n : ℕ) (hn : n ≠ 0) :
    (R ⧸ (maximalIdeal R ^ n)) ≃ₐ[R]
      (Henselization R ⧸ (maximalIdeal (Henselization R) ^ n)) :=
  AlgEquiv.ofBijective (quotientMaximalIdealPowMap R n)
    (quotientMaximalIdealPowMap_bijective R n hn)

end Henselization
