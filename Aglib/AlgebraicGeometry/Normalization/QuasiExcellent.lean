/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.RingTheory.Excellent.Normalization
public import Aglib.RingTheory.Excellent.FiniteNormalCompletion
public import Aglib.AlgebraicGeometry.Normalization.FunctionField.Finiteness

/-!
# Finite generic normalization of quasi-excellent surfaces

The hypothesis tests genuine quasi-excellence on the original nonempty affine
section rings, with auxiliary test universe zero. The conclusion concerns the
normalization of the original generic-point inclusion. No chosen global base,
Nagata assumption, replacement normalization, or resolution premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- An integral scheme of dimension at most two with genuine quasi-excellent
nonempty affine section rings has finite original generic normalization. -/
theorem genericNormalization_isFinite_of_isQuasiExcellentRing
    (W : Scheme.{u}) [IsIntegral W]
    (hdim : topologicalKrullDim W ≤ 2)
    (hQE : ∀ U : W.affineOpens, Nonempty U.1 →
      IsQuasiExcellentRing.{u, 0} Γ(W, U.1)) :
    IsFinite (W.fromSpecStalk (genericPoint W)).fromNormalization := by
  apply genericNormalization_isFinite_of_finite_app W
  intro U hne
  let : Nonempty U.1 := hne
  let γ := W.fromSpecStalk (genericPoint W)
  let := (γ.app U.1).hom.toAlgebra
  let : IsFractionRing Γ(W, U.1) Γ(Spec W.functionField, γ ⁻¹ᵁ U.1) :=
    genericSection_isFractionRing W U.1 U.2
  let : Field Γ(Spec W.functionField, γ ⁻¹ᵁ U.1) :=
    IsFractionRing.toField Γ(W, U.1)
  let : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  let : Ring.KrullDimLE 2 Γ(W, U.1) := Ring.krullDimLE_iff.mpr (by
    have h := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(W, U.1)) ≤ topologicalKrullDim W at h
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
    exact h.trans hdim)
  apply genericNormalization_finite_app_of_finite W U.1 U.2
  exact integralClosure.finite_of_isQuasiExcellentRing_of_dimLE_two
    Γ(W, U.1) (hQE U hne) Γ(Spec W.functionField, γ ⁻¹ᵁ U.1)

/-- At a dimension-two point of the original generic normalization, the
actual completed stalk is a normal domain under genuine affine QE hypotheses.
No global base or resolution is part of the input. -/
theorem genericNormalization_completion_normalDomain_of_dim_eq_two
    (W : Scheme.{u}) [IsIntegral W]
    (hdimW : topologicalKrullDim W ≤ 2)
    (hQE : ∀ U : W.affineOpens, Nonempty U.1 →
      IsQuasiExcellentRing.{u, 0} Γ(W, U.1))
    (y : (W.fromSpecStalk (genericPoint W)).normalization)
    (hdim : ringKrullDim
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y) = 2) :
    IsDomain (AdicCompletion
      (IsLocalRing.maximalIdeal
        ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y))
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)) ∧
    IsIntegrallyClosed (AdicCompletion
      (IsLocalRing.maximalIdeal
        ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y))
      ((W.fromSpecStalk (genericPoint W)).normalization.presheaf.stalk y)) := by
  let γ := W.fromSpecStalk (genericPoint W)
  let N := γ.normalization
  let ν : N ⟶ W := γ.fromNormalization
  let : IsFinite ν := genericNormalization_isFinite_of_isQuasiExcellentRing W hdimW hQE
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := ν y) (by trivial)
  let : Nonempty U := ⟨⟨ν y, hyU⟩⟩
  let V := ν ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage ν
  have hyV : y ∈ V := hyU
  let R := Γ(W, U)
  let S := Γ(N, V)
  let : Algebra R S := (ν.app U).hom.toAlgebra
  let : Module.Finite R S := ν.finite_app U hU
  let L := N.presheaf.stalk y
  let : IsDomain L := (genericNormalization_normalStalks W y).1
  let : IsIntegrallyClosed L := (genericNormalization_normalStalks W y).2
  let q := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  let : q.IsPrime := (hV.primeIdealOf ⟨y, hyV⟩).isPrime
  let : Algebra S L := N.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let : IsLocalization.AtPrime L q := hV.isLocalization_stalk ⟨y, hyV⟩
  let T := Localization.AtPrime q
  let e : T ≃ₐ[S] L := IsLocalization.algEquiv q.primeCompl T L
  let : IsDomain T := Function.Injective.isDomain e.toRingHom e.injective
  let : IsIntegrallyClosed T := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  obtain ⟨hdom, hnormal⟩ := AdicCompletion.normalDomain_of_finite_of_isGRing R S
    (hQE ⟨U, hU⟩ inferInstance).1 q (e.toRingEquiv.ringKrullDim.trans hdim)
  let : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal T) T) := hdom
  let : IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal T) T) := hnormal
  have hm : (IsLocalRing.maximalIdeal T).map e.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal L := IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  let ec : AdicCompletion (IsLocalRing.maximalIdeal T) T ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal L) L :=
    hm ▸ AdicCompletion.congrRingEquiv e.toRingEquiv (IsLocalRing.maximalIdeal T)
  exact ⟨Function.Injective.isDomain ec.symm.toRingHom ec.symm.injective,
    IsIntegrallyClosed.of_equiv ec⟩

end AlgebraicGeometry.Scheme
