/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsGoingDownPullback
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.NormalBase

/-! # Original Hartogs sections on a smooth punctured pullback

Normality of the smooth domain source, nonemptiness of its punctured
pullback, and the height-one condition are all constructed internally.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDomain B] [IsLocalRing A]

/-- An injective domain algebra map retains the original generic point over
the punctured spectrum of a positive-dimensional local base. -/
theorem puncturedPullback_nonempty_of_injective
    (hinj : Function.Injective (algebraMap A B)) (hdim : 2 ≤ ringKrullDim A) :
    Nonempty (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) := by
  refine ⟨⟨(⊥ : PrimeSpectrum B), ?_⟩⟩
  change PrimeSpectrum.comap (algebraMap A B) ⊥ ∈ puncturedSpecOpen A
  have hq : PrimeSpectrum.comap (algebraMap A B) ⊥ = ⊥ := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective (algebraMap A B) hinj
  rw [hq]
  intro he
  have hmax : IsLocalRing.maximalIdeal A = ⊥ :=
    (congrArg PrimeSpectrum.asIdeal he).symm
  have hd := hdim
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hmax, Ideal.height_bot] at hd
  norm_num at hd

/-- The unchanged scalar map on the actual punctured smooth pullback is
bijective. Source normality and all codimension conditions are conclusions
of the original smooth and normal-base hypotheses. -/
theorem hartogsSmoothPuncturedPullbackScalar_bijective
    [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.Smooth A B]
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (hartogsScalarMap B
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : IsIntegrallyClosed B := Algebra.Smooth.isIntegrallyClosed_of_normalBase A B
  let := puncturedPullback_nonempty_of_injective A B
    (FaithfulSMul.algebraMap_injective A B) hdim
  exact hartogsScalarMap_bijective B _
    (height_one_mem_puncturedGoingDownPullback A B hdim)

end AlgebraicGeometry.Scheme
