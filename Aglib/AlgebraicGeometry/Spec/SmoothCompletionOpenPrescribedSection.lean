/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsPrescribedSection
public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionHartogsOpen
public import Aglib.AlgebraicGeometry.Spec.SmoothSplitSectionFiniteEtaleMaps
public import Aglib.RingTheory.AdicCompletion.NoetherianRing

/-! # The prescribed completed section over an arbitrary ambient Hartogs open

The original open is retained throughout. The common Hartogs section-factor
construction supplies the extension; this is its thin completion instance.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual prescribed completed section lies in the etale locus, using
any original ambient Hartogs open whose section inverse image is punctured.
The intermediate completed-open etaleness premise is not a purity theorem. -/
theorem smoothCompletion_etaleAt_prescribedSection_of_open
    (A B : Type u) [CommRing A] [CommRing B]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Algebra A B] [Algebra.Smooth A B] (ε : B →ₐ[A] A)
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
    [FaithfulSMul B C] [Module.Finite B C] (U : (Spec (.of B)).Opens)
    (hheight : ∀ p : PrimeSpectrum B, p.asIdeal.height = 1 → p ∈ U)
    (hzero : splitSectionOpen ε.toRingHom U = puncturedSpecOpen A)
    (hdim : 2 ≤ ringKrullDim A) :
    let P := AdicCompletion (RingHom.ker ε.toRingHom) B
    let D := P ⊗[B] C
    ∀ (a : Spec (.of A) ⟶ Spec (.of D))
      (_ : a ≫ Spec.algebraMap P D = Spec.map (CommRingCat.ofHom
        (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)),
      ∀ [Etale (Spec.algebraMap P D ∣_ (Spec.algebraMap B P ⁻¹ᵁ U))],
      ∀ x : Spec (.of A), (Spec.algebraMap P D).etaleAt (a x) := by
  dsimp only
  intro a ha het
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let : IsNoetherianRing P := AdicCompletion.isNoetherianRing B (RingHom.ker ε.toRingHom)
  let : IsNoetherianRing D := IsNoetherianRing.of_finite P D
  let f : Spec (.of D) ⟶ Spec (.of P) := Spec.algebraMap P D
  let W : (Spec (.of P)).Opens := Spec.algebraMap B P ⁻¹ᵁ U
  let ζ : Spec (.of A) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom
    (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)
  obtain ⟨x⟩ := puncturedSpecOpen_nonempty A hdim
  have hx : x.val ∈ splitSectionOpen ε.toRingHom U := hzero.symm ▸ x.property
  let : Nonempty U := ⟨⟨Spec.map (CommRingCat.ofHom ε.toRingHom) x.val, hx⟩⟩
  let : IsFinite f := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap P D)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : Etale (f ∣_ W) := het
  have hWzero : ζ ⁻¹ᵁ W = puncturedSpecOpen A :=
    (smoothCompletionOpen_zeroSection A B ε U).trans hzero
  let : (FiniteEtale.baseChange (ζ ∣_ W)).Full :=
    (smoothSplitSectionPuncturedFiniteEtaleFullyFaithful ε W hdim hWzero).full
  have hW : Function.Bijective (affineScalarMap W.ι) :=
    smoothCompletionOpenScalar_bijective A B ε U hheight
  have hV : Function.Bijective (affineScalarMap (f ⁻¹ᵁ W).ι) :=
    smoothCompletionFiniteOpenScalar_bijective A B ε U C hheight
  have hp : Function.Bijective (affineScalarMap (puncturedSpecOpen A).ι) := by
    have h := puncturedSpecScalarMap_bijective A hdim
    rw [← affineScalarMap_topIso (puncturedSpecOpen A)] at h
    exact Function.Bijective.of_comp_left
      (f := (puncturedSpecOpen A).topIso.hom.hom)
      (g := affineScalarMap (puncturedSpecOpen A).ι) h
      (ConcreteCategory.bijective_of_isIso (puncturedSpecOpen A).topIso.hom).injective
  have hU : Function.Injective (affineScalarMap (ζ ⁻¹ᵁ W).ι) := hWzero.symm ▸ hp.injective
  exact etaleAt_prescribedSection_of_hartogs (algebraMap P D) W ζ a ha hW hV hU

end AlgebraicGeometry.Scheme
