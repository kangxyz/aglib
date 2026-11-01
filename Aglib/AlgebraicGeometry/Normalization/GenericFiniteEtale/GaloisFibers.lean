/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GaloisFibers
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback

/-! # Fibre transitivity for the original integral Galois cover

All field structures and the generic-source comparison are obtained from the
original cover and open immersion, not supplied as extra model premises.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ Spec (.of R)) [IsOpenImmersion j]
  (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left] [IsGalois Y]

include R j Y
/-- Original normalization fibre points lie in one orbit of actual over-base
isomorphisms; no field realization is a premise. -/
theorem genericNormalization_exists_iso_over_eq_of_image_eq
    (x y : (genericMap j Y.obj.hom).normalization)
    (h : (genericMap j Y.obj.hom).fromNormalization x =
      (genericMap j Y.obj.hom).fromNormalization y) :
    ∃ e : (genericMap j Y.obj.hom).normalization ≅
        (genericMap j Y.obj.hom).normalization,
      e.hom ≫ (genericMap j Y.obj.hom).fromNormalization =
        (genericMap j Y.obj.hom).fromNormalization ∧ e.hom x = y := by
  let K := U.functionField
  let L := Y.obj.left.functionField
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  let : Algebra R (Spec (.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : Algebra R K := ((functionFieldMap j).comp
    (algebraMap R (Spec (.of R)).functionField)).toAlgebra
  let : Algebra K L := GenericGalois.algebra Y
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let a : (Spec (.of R)).functionField ≃ₐ[R] K :=
    { FunctionField.fieldEquiv j with commutes' := fun _ => rfl }
  let : IsFractionRing R (Spec (.of R)).functionField :=
    functionField_isFractionRing_of_affine (.of R)
  let : IsFractionRing R K := IsLocalization.isLocalization_of_algEquiv _ a
  let : Module.Finite K L := (GenericGalois.functionField_finiteEtale Y).1
  let : _root_.IsGalois K L := GenericGalois.functionField_isGalois Y
  have hc : (originalFieldSpectrumIso j Y).hom ≫ genericMap j Y.obj.hom =
      Spec.algebraMap R L := by
    rw [originalFieldSpectrumIso_hom_genericMap,
      ← Category.assoc, fromSpecStalk_genericPoint_naturality Y.obj.hom]
    rw [Category.assoc, fromSpecStalk_genericPoint_naturality j,
      Spec.fromSpecStalk_eq']
    change Spec.map (CommRingCat.ofHom (functionFieldMap Y.obj.hom)) ≫
      Spec.map (CommRingCat.ofHom (functionFieldMap j)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Spec (.of R)).functionField)) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact Hom.normalization_exists_iso_over_eq_of_image_eq R K L
    (genericMap j Y.obj.hom) (originalFieldSpectrumIso j Y) hc x y h

/-- Etaleness propagates in the same original normalization fibre. -/
theorem genericNormalization_etaleAt_of_image_eq
    (x y : (genericMap j Y.obj.hom).normalization)
    (h : (genericMap j Y.obj.hom).fromNormalization x =
      (genericMap j Y.obj.hom).fromNormalization y)
    (hx : (genericMap j Y.obj.hom).fromNormalization.etaleAt x) :
    (genericMap j Y.obj.hom).fromNormalization.etaleAt y := by
  obtain ⟨e, he, hp⟩ := genericNormalization_exists_iso_over_eq_of_image_eq R j Y x y h
  simpa only [hp] using hx.map_over_iso e he

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
