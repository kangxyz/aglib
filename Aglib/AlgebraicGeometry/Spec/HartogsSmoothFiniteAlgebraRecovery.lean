/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsSmoothFiniteBaseChange
public import Aglib.AlgebraicGeometry.Spec.HartogsOpenEnlargement
public import Aglib.AlgebraicGeometry.Spec.ScalarMapFaithfulness
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Recovery of the same finite normal algebra after flat base change

The new algebra is literally P tensor_B C. Its scalar map on the original
punctured-base inverse image is bijective by the original normal Hartogs
producer. Enlargement gives the same assertion over the specified larger
open. The resulting canonical scalar isomorphism transfers etaleness back
to that same tensor algebra. No normalization or domain premise is imposed
on the new rings, and no comparison certificate is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- The original structural scalar triangle, with the literal restricted
finite-algebra morphism and unchanged tensor algebra. -/
theorem smoothFiniteTensorScalar_triangle
    (B C P : Type u) [CommRing B] [CommRing C] [CommRing P]
    [Algebra B C] [Algebra B P] (V : (Spec (.of P)).Opens) :
    affineScalarMap ((Spec.algebraMap P (P ⊗[B] C) ∣_ V) ≫ V.ι) =
      (affineScalarMap (Spec.algebraMap P (P ⊗[B] C) ⁻¹ᵁ V).ι).comp
        (algebraMap P (P ⊗[B] C)) := by
  rw [morphismRestrict_ι]
  exact affineScalarMap_comp_specMap
    (Spec.algebraMap P (P ⊗[B] C) ⁻¹ᵁ V).ι (algebraMap P (P ⊗[B] C))

variable (A B C P : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing P]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
  [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
  [FaithfulSMul B C] [Module.Finite B C]
  [Algebra B P] [Module.Flat B P] [IsNoetherianRing P]

local notation "T" => P ⊗[B] C
local notation "t" => Spec.algebraMap P T
local notation "b" => Spec.algebraMap B P

/-- The actual original finite-algebra base change has bijective scalar
restriction on every specified open containing the original puncture pullback. -/
theorem smoothFiniteTensorScalar_bijective
    (hdim : 2 ≤ ringKrullDim A) (V : (Spec (.of P)).Opens)
    (hV : b ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) ≤ V) :
    Function.Bijective (affineScalarMap (t ⁻¹ᵁ V).ι) := by
  let : IsNoetherianRing T := IsNoetherianRing.of_finite P T
  let σ : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hσ : σ.Flat := by
    have h := (RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat C (C ⊗[B] P))).comp
        (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm B C P).bijective)
    have he : σ = (Algebra.TensorProduct.comm B C P).toRingHom.comp
        (algebraMap C (C ⊗[B] P)) := by
      apply RingHom.ext
      intro c
      change (1 ⊗ₜ[B] c) = (Algebra.TensorProduct.comm B C P) (c ⊗ₜ[B] (1 : P))
      exact (Algebra.TensorProduct.comm_tmul B c (1 : P)).symm
    exact he.symm ▸ h
  let k := Spec.map (CommRingCat.ofHom σ)
  let W := Spec.algebraMap B C ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)
  have hsmall : Function.Bijective (affineScalarMap (k ⁻¹ᵁ W).ι) :=
    hartogsSmoothFiniteScalar_bijective_of_flat A B C hdim σ hσ
      (k ∣_ W) (k ⁻¹ᵁ W).ι (isPullback_morphismRestrict k W)
  have hsquare : k ≫ Spec.algebraMap B C = t ≫ b := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (Algebra.TensorProduct.includeRight.commutes r).trans
      (IsScalarTower.algebraMap_apply B P T r).symm
  have hle : k ⁻¹ᵁ W ≤ t ⁻¹ᵁ V := by
    change k ⁻¹ᵁ (Spec.algebraMap B C ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)) ≤ t ⁻¹ᵁ V
    rw [← Hom.comp_preimage, hsquare, Hom.comp_preimage]
    exact fun x hx => hV hx
  exact affineScalarMap_bijective_of_hartogs_open_le T (k ⁻¹ᵁ W)
    (t ⁻¹ᵁ V) hle hsmall

/-- Etaleness of the original cover-section algebra transfers to the same
original tensor algebra, through its proved canonical scalar isomorphism.
The section-algebra etaleness input is supplied by the actual conditional
power-series effectivity consumer; it is not a final relative-purity premise. -/
theorem smoothFiniteTensor_etale_of_sectionScalar_etale
    (hdim : 2 ≤ ringKrullDim A) (V : (Spec (.of P)).Opens)
    (hV : b ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) ≤ V)
    (he : (affineScalarMap ((t ∣_ V) ≫ V.ι)).Etale) :
    (algebraMap P T).Etale := by
  let q := CommRingCat.ofHom (affineScalarMap (t ⁻¹ᵁ V).ι)
  let : IsIso q := (ConcreteCategory.isIso_iff_bijective q).mpr
    (smoothFiniteTensorScalar_bijective A B C P hdim V hV)
  let : IsIso (Spec.map q) := inferInstance
  have htriangle : Spec.map q ≫ t =
      Spec.map (CommRingCat.ofHom (affineScalarMap ((t ∣_ V) ≫ V.ι))) := by
    rw [← Spec.map_comp, smoothFiniteTensorScalar_triangle B C P V]
    rfl
  have hwhole : Etale (Spec.map q ≫ t) := by
    rw [htriangle]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  let := hwhole
  have hback : Etale ((asIso (Spec.map q)).inv ≫ (Spec.map q ≫ t)) := inferInstance
  have hc : (asIso (Spec.map q)).inv ≫ (Spec.map q ≫ t) = t :=
    (asIso (Spec.map q)).inv_hom_id_assoc t
  have ht : Etale t := hc ▸ hback
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp ht

end AlgebraicGeometry.Scheme
