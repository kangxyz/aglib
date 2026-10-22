/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Lift
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Actual points on modifications at residue centres

Residue vanishing constructs divisibility witnesses and hence the original
point on the modification. Agreement on the original coefficients determines
maps into targets where the distinguished element is regular.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

/-- Ring maps out of the actual modification are determined by their values on
original coefficients when the image of the distinguished element is regular. -/
theorem ringHom_ext_of_isRegular {B C ι : Type*} [CommRing B] [CommRing C]
    (p : B) (g : ι → B) (φ ψ : Modification p g →+* C)
    (hp : IsRegular (φ (of p g p)))
    (hcoeff : ∀ b, φ (of p g b) = ψ (of p g b)) : φ = ψ := by
  let f := φ.comp (of p g)
  let z := fun i => φ (coordinate p g i)
  have hz (i : ι) : f p * z i = f (g i) := by
    change φ (of p g p) * φ (coordinate p g i) = φ (of p g (g i))
    rw [← map_mul, of_mul_coordinate]
  apply (lift_unique p g f z hz hp φ rfl).trans
  apply (lift_unique p g f z hz hp ψ ?_).symm
  ext b
  exact (hcoeff b).symm

/-- Actual residue vanishing gives an actual lift of the original point; no
choice of divisible coordinates is required as input. -/
theorem exists_lift_of_residue_eq_zero {R B S ι : Type*}
    [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [IsDomain S] [IsDiscreteValuationRing S]
    (p : R) (g : ι → B) (χ : B →ₐ[R] S)
    (hp : Irreducible (algebraMap R S p))
    (hg : ∀ i, IsLocalRing.residue S (χ (g i)) = 0) :
    ∃ χ' : Modification (algebraMap R B p) g →ₐ[R] S,
      ∀ b, χ' (of (algebraMap R B p) g b) = χ b := by
  classical
  have hd (i : ι) : algebraMap R S p ∣ χ (g i) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hp.maximalIdeal_eq]
    exact (IsLocalRing.residue_eq_zero_iff _).mp (hg i)
  choose z hz using hd
  have hz' (i : ι) : χ.toRingHom (algebraMap R B p) * z i = χ.toRingHom (g i) := by
    change χ (algebraMap R B p) * z i = χ (g i)
    rw [χ.commutes]
    exact (hz i).symm
  have hreg : IsRegular (χ.toRingHom (algebraMap R B p)) := by
    change IsRegular (χ (algebraMap R B p))
    rw [χ.commutes]
    exact isRegular_iff_ne_zero.mpr hp.ne_zero
  let χ' : Modification (algebraMap R B p) g →ₐ[R] S :=
    { toRingHom := lift (algebraMap R B p) g χ.toRingHom z hz' hreg
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R B (Modification (algebraMap R B p) g)]
        change lift (algebraMap R B p) g χ.toRingHom z hz' hreg
          (of (algebraMap R B p) g (algebraMap R B r)) = algebraMap R S r
        exact (lift_of (algebraMap R B p) g χ.toRingHom z hz' hreg
          (algebraMap R B r)).trans (χ.commutes r) }
  exact ⟨χ', fun b => lift_of (algebraMap R B p) g χ.toRingHom z hz' hreg b⟩

end Algebra.NeronModification
