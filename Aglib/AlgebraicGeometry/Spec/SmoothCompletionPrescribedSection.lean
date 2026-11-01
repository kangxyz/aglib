/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsPrescribedSection
public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionHartogs
public import Aglib.AlgebraicGeometry.Spec.SmoothSplitSectionFiniteEtaleMaps
public import Aglib.RingTheory.AdicCompletion.NoetherianRing

/-! # The prescribed section of the original smooth completion

The actual completion and its finite algebra tensor product retain the
prescribed section. Etaleness on their punctured open is an explicit input
of this intermediate assembly, not a new hypothesis in relative purity.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- Original punctured etaleness on the completion gives etaleness along
its prescribed closed section. All scalar and fullness inputs are constructed
from the original normal local base and smooth split algebra. -/
theorem smoothCompletion_etaleAt_prescribedSection
    (A B : Type u) [CommRing A] [CommRing B]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Algebra A B] [Algebra.Smooth A B] (ε : B →ₐ[A] A)
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
    [FaithfulSMul B C] [Module.Finite B C] (hdim : 2 ≤ ringKrullDim A) :
    let P := AdicCompletion (RingHom.ker ε.toRingHom) B
    let D := P ⊗[B] C
    ∀ (a : Spec (.of A) ⟶ Spec (.of D))
      (_ : a ≫ Spec.algebraMap P D = Spec.map (CommRingCat.ofHom
        (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)),
      ∀ [Etale (Spec.algebraMap P D ∣_
        (Spec.algebraMap A P ⁻¹ᵁ puncturedSpecOpen A))],
      ∀ x : Spec (.of A), (Spec.algebraMap P D).etaleAt (a x) := by
  dsimp only
  intro a ha het
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let : IsNoetherianRing P := AdicCompletion.isNoetherianRing B (RingHom.ker ε.toRingHom)
  let : IsNoetherianRing D := IsNoetherianRing.of_finite P D
  let f : Spec (.of D) ⟶ Spec (.of P) := Spec.algebraMap P D
  let W : (Spec (.of P)).Opens := Spec.algebraMap A P ⁻¹ᵁ puncturedSpecOpen A
  let ζ : Spec (.of A) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom
    (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)
  let : IsFinite f := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap P D)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : Etale (f ∣_ W) := het
  have hzero : ζ ⁻¹ᵁ W = puncturedSpecOpen A :=
    smoothCompletionPuncturedOpen_zeroSection A B ε
  let : (FiniteEtale.baseChange (ζ ∣_ W)).Full :=
    (smoothSplitSectionPuncturedFiniteEtale_fullyFaithful ε W hdim hzero).full
  have hW : Function.Bijective (affineScalarMap W.ι) :=
    smoothCompletionPuncturedScalar_bijective A B ε hdim
  have hV : Function.Bijective (affineScalarMap (f ⁻¹ᵁ W).ι) :=
    smoothCompletionFinitePuncturedScalar_bijective A B ε C hdim
  have hp : Function.Bijective (affineScalarMap (puncturedSpecOpen A).ι) := by
    have h := puncturedSpecScalarMap_bijective A hdim
    rw [← affineScalarMap_topIso (puncturedSpecOpen A)] at h
    exact Function.Bijective.of_comp_left
      (f := (puncturedSpecOpen A).topIso.hom.hom)
      (g := affineScalarMap (puncturedSpecOpen A).ι) h
      (ConcreteCategory.bijective_of_isIso (puncturedSpecOpen A).topIso.hom).injective
  have hU : Function.Injective (affineScalarMap (ζ ⁻¹ᵁ W).ι) := hzero.symm ▸ hp.injective
  exact etaleAt_prescribedSection_of_hartogs (algebraMap P D) W ζ a ha hW hV hU

end AlgebraicGeometry.Scheme
