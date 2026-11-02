/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Etale
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Regular parameters under essentially etale local maps

The actual flat local map preserves the given nonzerodivisor. Its quotient
map is the original base change; formal unramifiedness and essential finite
type transfer regularity to that quotient. No finite-presentation assumption
on the local map, domain assumption, or chosen local model is needed.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Algebra.FormallyUnramified

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
  [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
  [Module.Flat R S] [FormallyUnramified R S]

/-- The original regular parameter and its regular principal quotient ascend
along the original essentially etale local map. Target Noetherianity is derived. -/
theorem regularParameter_of_flat (f : R) (hf : f ∈ maximalIdeal R)
    (hreg : IsSMulRegular R f) [IsRegularLocalRing (R ⧸ Ideal.span {f})] :
    IsNoetherianRing S ∧ IsRegularLocalRing S ∧
      algebraMap R S f ∈ maximalIdeal S ∧ IsSMulRegular S (algebraMap R S f) ∧
      IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S f}) := by
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularLocalRing S := Algebra.FormallyUnramified.isRegularLocalRing_of_flat R S
  have hfS : algebraMap R S f ∈ maximalIdeal S := by
    intro hunit
    exact hf (isUnit_of_map_unit (algebraMap R S) f hunit)
  have hregS : IsSMulRegular S (algebraMap R S f) := hreg.of_flat
  refine ⟨inferInstance, inferInstance, hfS, hregS, ?_⟩
  let I : Ideal R := Ideal.span {f}
  let J : Ideal S := I.map (algebraMap R S)
  have hJ : J = Ideal.span {algebraMap R S f} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
  have hJproper : J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
    rw [hJ]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfS)
  let Q := S ⧸ J
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJproper
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap (R ⧸ I) Q) := by
    constructor
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change IsUnit (Ideal.Quotient.mk J (algebraMap R S r)) at ha
    exact (isUnit_of_map_unit (algebraMap R S) r
      (isUnit_of_map_unit (Ideal.Quotient.mk J) _ ha)).map (Ideal.Quotient.mk I)
  let : Module.Flat (R ⧸ I) Q := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  have hQ : IsRegularLocalRing Q :=
    Algebra.FormallyUnramified.isRegularLocalRing_of_flat (R ⧸ I) Q
  change IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S f})
  rw [← hJ]
  exact hQ

end Algebra.FormallyUnramified
