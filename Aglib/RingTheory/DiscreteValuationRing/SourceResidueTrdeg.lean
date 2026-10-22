/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.SourceFractionParameters
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The original source fraction degree bounds its actual centre parameters

Localizing at the actual centre supplies lifts of residue parameters. They are
mapped directly into the ORIGINAL fraction field, so no generic-coordinate
fraction tower or new separability hypothesis is needed.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace ParameterLocalization.SourceCentre

universe u v w t
variable {R : Type u} {S : Type v} {B : Type w}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- The actual source centre is the inverse image of the target maximal ideal
under the original source point. -/
abbrev centre (χ : B →ₐ[R] S) : Ideal B := (maximalIdeal S).comap χ.toRingHom
/-- The original source localized at the inverse image of the target maximal
ideal under the prescribed source point. -/
abbrev LocalSource (χ : B →ₐ[R] S) := Localization.AtPrime (centre χ)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain B]
  [IsLocalHom (algebraMap R S)] in
/-- Every actual denominator maps to a unit at the target. -/
theorem denominator_unit (χ : B →ₐ[R] S) (s : (centre χ).primeCompl) :
    IsUnit (χ s) := by
  exact not_not.mp s.property

/-- The original source point extends across its actual centre. -/
def localPoint (χ : B →ₐ[R] S) : LocalSource χ →ₐ[R] S :=
  IsLocalization.liftAlgHom (denominator_unit χ)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain B]
  [IsLocalHom (algebraMap R S)] in
@[simp] theorem localPoint_algebraMap (χ : B →ₐ[R] S) (b : B) :
    localPoint χ (algebraMap B (LocalSource χ) b) = χ b :=
  IsLocalization.lift_eq _ b

instance localPoint_isLocalHom (χ : B →ₐ[R] S) : IsLocalHom (localPoint χ) := by
  have hm : maximalIdeal (LocalSource χ) ≤ (maximalIdeal S).comap (localPoint χ) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (centre χ) (LocalSource χ)]
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change localPoint χ (algebraMap B (LocalSource χ) b) ∈ maximalIdeal S
    rw [localPoint_algebraMap]
    exact hb
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  exact (hm hn) hx

instance coefficient_isLocalHom (χ : B →ₐ[R] S) :
    IsLocalHom (algebraMap R (LocalSource χ)) := by
  refine ⟨fun r hr => ?_⟩
  apply isUnit_of_map_unit (algebraMap R S) r
  have h := (localPoint χ).isUnit_map hr
  change IsUnit (localPoint χ (algebraMap R (LocalSource χ) r)) at h
  rwa [AlgHom.commutes] at h

/-- The localization has its canonical injection into the original fraction field. -/
def originalFractionMap (χ : B →ₐ[R] S) : LocalSource χ →ₐ[R] FractionRing B :=
  IsLocalization.liftAlgHom (f := IsScalarTower.toAlgHom R B (FractionRing B))
    (fun s : (centre χ).primeCompl =>
      IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective B (FractionRing B))
        (⟨s, (centre χ).primeCompl_le_nonZeroDivisors s.property⟩ : nonZeroDivisors B))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsLocalHom (algebraMap R S)] in
theorem originalFractionMap_injective (χ : B →ₐ[R] S) :
    Function.Injective (originalFractionMap χ) := by
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  rw [(IsLocalization.injective (LocalSource χ)
    (centre χ).primeCompl_le_nonZeroDivisors).eq_iff]
  change x = y ↔ algebraMap B (FractionRing B) x = algebraMap B (FractionRing B) y
  exact (IsFractionRing.injective B (FractionRing B)).eq_iff.symm

/-- A genuine residue-field independent family has cardinality bounded by the
transcendence degree of the ORIGINAL source fraction extension. -/
theorem residue_independent_trdeg_bound {ι : Type t} [Finite ι]
    (p : R) [Fact (Irreducible p)] (χ : B →ₐ[R] S)
    (hpS : Irreducible (algebraMap R S p)) (x : ι → ResidueField (LocalSource χ))
    (hx : AlgebraicIndependent (ResidueField R) x) :
    letI : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
    letI : Algebra (FractionRing R) (FractionRing B) :=
      FractionRing.liftAlgebra R (FractionRing B)
    Cardinal.lift.{w} (Cardinal.mk ι) ≤
      Cardinal.lift.{t} (Algebra.trdeg (FractionRing R) (FractionRing B)) := by
  let : FaithfulSMul R B := faithfulSMul_source_of_map_irreducible p χ hpS
  let : Algebra (FractionRing R) (FractionRing B) :=
    FractionRing.liftAlgebra R (FractionRing B)
  let : IsScalarTower R (FractionRing R) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing B)
  choose b hb using fun i => residue_surjective (x i)
  have hres : AlgebraicIndependent (ResidueField R)
      (fun i => residue S (localPoint χ (b i))) := by
    have h := hx.map' (f := ResidueField.mapAlgHom' (localPoint χ))
      (ResidueField.mapAlgHom' (localPoint χ)).injective
    simpa only [Function.comp_def, ← hb, ResidueField.mapAlgHom'_residue] using h
  have hs : AlgebraicIndependent R b :=
    AlgebraicIndependent.of_comp (localPoint χ)
      (algebraicIndependent_of_residue p (localPoint χ ∘ b) hres hpS)
  have hf : AlgebraicIndependent R (originalFractionMap χ ∘ b) :=
    hs.map' (f := originalFractionMap χ) (originalFractionMap_injective χ)
  exact (hf.localization (nonZeroDivisors R)).lift_cardinalMk_le_trdeg

end ParameterLocalization.SourceCentre
