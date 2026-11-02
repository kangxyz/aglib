/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.Defs
public import Aglib.RingTheory.Excellent.RegularLocus
public import Aglib.RingTheory.AdicCompletion.Normalization
public import Aglib.RingTheory.IntegralClosure.FiniteLocalization
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Aglib.RingTheory.RegularLocalRing.Reduced
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Finite normalization of quasi-excellent domains in dimension at most two

The generic regular fibre of a regular map from a domain contains the target
injectively, by flatness. Applied to the original completion map this supplies
reduced completion, hence local N-1 in dimension at most two. The global theorem
uses a nonzero normal principal open and the actual maximal-local normalization
patching theorem; pointwise finite generation alone is not used as a patching
criterion. Only the explicit auxiliary test universe zero is used for J-2.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Algebra.IsRegularMap

/-- A regular map from a domain has reduced target: flatness embeds the target
into its regular generic fibre, with its original coefficient map. -/
theorem isReduced_of_isDomain
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] (h : Algebra.IsRegularMap R S) : IsReduced S := by
  let : Module.Flat R S := h.1
  let : IsRegularRing (S ⊗[R] FractionRing R) :=
    h.regular_finiteGenericFibre R S (FractionRing R) (FractionRing R)
  let : IsReduced (S ⊗[R] FractionRing R) :=
    IsRegularRing.isReduced_of_regular _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] FractionRing R)
    (Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R)))

end Algebra.IsRegularMap

namespace integralClosure

/-- A domain of dimension at most two with regular actual maximal-adic
completion map has finite normalization in its supplied fraction ring. -/
theorem finite_of_regular_completion_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R]
    (h : Algebra.IsRegularMap R (AdicCompletion (maximalIdeal R) R))
    (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) :=
  finite_of_isReduced_completion_of_dimLE_two R
    (h.isReduced_of_isDomain R _) K

/-- The G-ring condition and a nonempty regular open suffice for finite
normalization of a domain in dimension at most two. The local fraction-field
maps are the actual localization lifts into the original supplied field. -/
theorem finite_of_isGRing_of_isJ0Ring_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [Ring.KrullDimLE 2 R]
    (hG : IsGRing R) (hJ : IsJ0Ring R)
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let : IsNoetherianRing R := hG.1
  obtain ⟨f, hf, hreg⟩ := (IsJ0Ring.iff_exists_regular_away R).mp hJ
  let : IsRegularRing (Localization.Away f) := hreg
  let : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  let : IsIntegrallyClosed (Localization.Away f) :=
    IsIntegrallyClosed.of_localization_maximal
      (fun p _ _ => IsRegularLocalRing.isIntegrallyClosed_of_regularLocal
        (Localization.AtPrime p))
  apply finite_of_normal_away_of_finite_atMaximal R K f hf
  intro m hm
  let : m.IsMaximal := hm
  let B := Localization.AtPrime m
  let φ : B →ₐ[R] K := atPrimeFractionMap R K m
  let : Algebra B K := φ.toRingHom.toAlgebra
  let : IsScalarTower R B K := IsScalarTower.of_algHom φ
  let : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl B K
  let : Ring.KrullDimLE 2 B := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m B]
    exact (ringKrullDim_le_iff_height_le _).mp
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)) inferInstance)
  exact finite_of_regular_completion_of_dimLE_two B (hG.2 m) K

/-- A genuine quasi-excellent domain in dimension at most two is N-1.
This does not assert Nagata/N-2 or normality of completed normalization stalks. -/
theorem finite_of_isQuasiExcellentRing_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [Ring.KrullDimLE 2 R]
    (h : IsQuasiExcellentRing.{u, 0} R)
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Finite R (integralClosure R K) := by
  let : IsNoetherianRing R := h.1.1
  apply finite_of_isGRing_of_isJ0Ring_of_dimLE_two R h.1 ?_ K
  exact ⟨inferInstance, PrimeSpectrum.regularLocus R, h.2.2 R,
    PrimeSpectrum.regularLocus_nonempty R, Set.Subset.rfl⟩

end integralClosure
