/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.HeightOneRootLocalization
public import Aglib.RingTheory.IntegralClosure.FiniteEtale.GoingDown
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # The specified height-one prime of the actual normalization

The finite-etale generic algebra may be disconnected. Going down for its
actual normalization retains the specified source prime without imposing a
domain hypothesis on that normalization. Its contraction identifies the
original root localization with coefficient localization at the parameter.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

universe u v w

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (f : R) [IsRegularLocalRing (R ⧸ Ideal.span {f})]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- A regular parameter quotient makes its original defining ideal prime. -/
theorem regularParameter_span_isPrime : (Ideal.span {f} : Ideal R).IsPrime := by
  let : IsDomain (R ⧸ Ideal.span {f}) := IsRegularLocalRing.isDomain_of_regularLocal _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- The literal parameter-prime localization is a domain, by regularity of
its original base; no Henselianity of this localization is asserted. -/
theorem parameterPrime_isDomain (hreg : IsSMulRegular R f) :
    letI := regularParameter_span_isPrime R f
    IsDomain (Localization.AtPrime (Ideal.span {f} : Ideal R)) := by
  let := regularParameter_span_isPrime R f
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  infer_instance

/-- The image of the original parameter is an actual uniformizer at its
original prime. -/
theorem parameterPrime_irreducible (hreg : IsSMulRegular R f) :
    letI := regularParameter_span_isPrime R f
    Irreducible (algebraMap R (Localization.AtPrime (Ideal.span {f} : Ideal R)) f) := by
  let := regularParameter_span_isPrime R f
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let D := Localization.AtPrime (Ideal.span {f} : Ideal R)
  have hf0 : f ≠ 0 := by
    intro hz
    have he : (1 : R) = 0 := hreg (by simp [hz])
    exact one_ne_zero he
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact (map_ne_zero_iff _ (IsLocalization.injective D
      (Ideal.span {f} : Ideal R).primeCompl_le_nonZeroDivisors)).mpr hf0
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]

/-- The actual localization at the parameter prime is a DVR. Regularity is
used only in the original ring; no strict-henselization Noetherianity is assumed. -/
theorem parameterPrime_isDiscreteValuationRing (hreg : IsSMulRegular R f) :
    letI := regularParameter_span_isPrime R f
    letI := parameterPrime_isDomain R f hreg
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f} : Ideal R)) := by
  let := regularParameter_span_isPrime R f
  let := parameterPrime_isDomain R f hreg
  let D := Localization.AtPrime (Ideal.span {f} : Ideal R)
  have hirr := parameterPrime_irreducible R f hreg
  have hm : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D f} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hn : IsLocalRing.maximalIdeal D ≠ ⊥ := by
    rw [hm, ne_eq, Ideal.span_singleton_eq_bot]
    exact hirr.ne_zero
  have hfield : ¬ IsField D := IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hn
  apply ((IsDiscreteValuationRing.TFAE D hfield).out 5 1).mp
  rw [hm]
  infer_instance

variable (hf : f ∈ IsLocalRing.maximalIdeal R) (N : ℕ) (hN : 0 < N)
  (hreg : IsSMulRegular R f)
  (F : Type v) [Field F] [Algebra (RootAlgebra N f) F]
  [IsFractionRing (RootAlgebra N f) F]
  (A : Type w) [CommRing A] [Algebra F A] [Algebra (RootAlgebra N f) A]
  [IsScalarTower (RootAlgebra N f) F A] [Algebra.Etale F A]

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)

include hf hN hreg F in
/-- A specified height-one prime over the root contracts to the original root
ideal even when the actual normalization is disconnected. -/
theorem normalized_parameterRoot_heightOne_under_eq
    (q : Ideal (integralClosure T A)) [q.IsPrime] (hq : q.height = 1)
    (hdiv : algebraMap T (integralClosure T A) θ ∈ q) :
    q.under T = Ideal.span {θ} := by
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsIntegrallyClosed T := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal T
  let : Module.Finite R T := root_finite N hN f
  let : IsNoetherianRing T := inferInstance
  let : Algebra.HasGoingDown T (integralClosure T A) :=
    integralClosure.hasGoingDown_of_etale T F A
  have hp : (q.under T).height = 1 :=
    (Ideal.height_eq_height_under q).symm.trans hq
  exact Ideal.eq_span_singleton_of_height_eq_one hp hdiv
    (parameterRoot_root_prime R f hf N hN hreg)

include hf hN hreg F in
/-- The actual coefficient-localized root is the localization at the
contraction of the specified normalization prime. -/
theorem normalized_parameterRoot_isLocalizationAtPrime
    (q : Ideal (integralClosure T A)) [q.IsPrime] (hq : q.height = 1)
    (hdiv : algebraMap T (integralClosure T A) θ ∈ q) :
    letI := regularParameter_span_isPrime R f
    let D := Localization.AtPrime (Ideal.span {f} : Ideal R)
    letI := rootBaseChangeAlgebra D N f
    IsLocalization.AtPrime (RootAlgebra N (algebraMap R D f)) (q.under T) := by
  let := regularParameter_span_isPrime R f
  let : (Ideal.span {θ} : Ideal T).IsPrime :=
    (Ideal.span_singleton_prime (parameterRoot_root_prime R f hf N hN hreg).ne_zero).mpr
      (parameterRoot_root_prime R f hf N hN hreg)
  have heq := normalized_parameterRoot_heightOne_under_eq R f hf N hN hreg F A q hq hdiv
  simpa only [heq] using (parameterLocalizedRoot_isLocalizationAtPrime N f hN)

end Algebra.Kummer
