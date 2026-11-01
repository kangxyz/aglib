/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsSmoothPullback
public import Aglib.AlgebraicGeometry.Spec.HartogsIntegralBaseChange

/-! # Flat base change of the original finite normal smooth Hartogs extension

The original finite normal algebra retains all its scalar sections over the
punctured-base inverse image, including after arbitrary flat base change.
The new algebra is not assumed normal, a domain, or a chosen normalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A finite normal domain over a smooth domain has the original Hartogs
section identification after any flat scalar base change. Every normality,
Noetherianity, and codimension premise concerning the smooth ambient algebra
is derived from the original base hypotheses. -/
theorem hartogsSmoothFiniteScalar_bijective_of_flat
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
    [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
    [FaithfulSMul B C] [Module.Finite B C]
    (hdim : 2 ≤ ringKrullDim A)
    {T : Type u} [CommRing T] (σ : C →+* T) (hσ : σ.Flat)
    {Y : Scheme.{u}}
    (p : Y ⟶ (Spec.algebraMap B C ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)).toScheme)
    (q : Y ⟶ Spec (.of T))
    (H : IsPullback p q (Spec.algebraMap B C ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)).ι
      (Spec.map (CommRingCat.ofHom σ))) : Function.Bijective (affineScalarMap q) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  let : IsIntegrallyClosed B := Algebra.Smooth.isIntegrallyClosed_of_normalBase A B
  let := puncturedPullback_nonempty_of_injective A B
    (FaithfulSMul.algebraMap_injective A B) hdim
  exact hartogsIntegralPullbackAffineScalar_bijective_of_flat B C
    (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)
    (height_one_mem_puncturedGoingDownPullback A B hdim) σ hσ p q H

end AlgebraicGeometry.Scheme
