/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.RationalAdjunction.General

/-! # Dimension-two compatibility for general rational-adjunction normalization -/

@[expose] public noncomputable section

open IsLocalRing Polynomial Module.associatedPrimes

universe u

namespace AdicCompletion

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual maximal-local completion of a rational adjunction is reduced
when its generator is nonzero and lies in the selected maximal ideal. -/
theorem isReduced_atMaximal_adjoin_singleton_of_mem
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (hx : x ≠ 0)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hxm : Algebra.adjoinSingletonGenerator R x ∈ m) :
    IsReduced (AdicCompletion
      (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)) := by
  have := hdim
  exact isReduced_atMaximal_adjoin_singleton_of_generator_mem R K hR x hx m hxm

end AdicCompletion

namespace integralClosure

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Finite normalization of the actual selected local ring, in the original
fraction field with the original localization lift as coefficient action. -/
theorem finite_atMaximal_adjoin_singleton_of_mem
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (hx : x ≠ 0)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hxm : Algebra.adjoinSingletonGenerator R x ∈ m) :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  have := hdim
  exact finite_atMaximal_adjoin_singleton_of_generator_mem R K hR x hx m hxm

end integralClosure

namespace integralClosure

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A monic residue relation reduces the original maximal local ring to
the nonzero-generator local case through a finite birational algebra and
then a second localization. -/
theorem finite_atMaximal_adjoin_singleton_of_monic
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (f : R[X]) (hf : f.Monic)
    (hfm : aeval (Algebra.adjoinSingletonGenerator R x) f ∈ m) :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  have := hdim
  exact finite_atMaximal_adjoin_singleton_of_monic_relation R K hR x m f hf hfm

end integralClosure

namespace integralClosure

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every maximal localization of an actual rational adjunction over a
normal Nagata surface ring has finite normalization in the supplied field. -/
theorem finite_atMaximal_adjoin_singleton_of_dimLE_two
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  have := hdim
  exact finite_atMaximal_adjoin_singleton R K hR x m

end integralClosure

namespace integralClosure

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Finite literal normalization of a rational adjunction over a normal
Nagata domain of dimension at most two, in the original supplied field. -/
theorem finite_adjoin_singleton_of_isNagataRing_dimLE_two
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) (x : K) :
    Module.Finite (Algebra.adjoin R ({x} : Set K))
      (integralClosure (Algebra.adjoin R ({x} : Set K)) K) := by
  have := hdim
  exact finite_adjoin_singleton_of_isNagataRing R K hR x

end integralClosure
