/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FiniteGenericSubalgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Canonical generic squares for the finite separable intermediate algebra -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Algebra.FiniteGenericSubalgebra

namespace AlgebraicGeometry.Scheme.FiniteGenericSubalgebra

universe u

variable (R K A A' : Type u) [CommRing R] [Field K] [CommRing A] [CommRing A']
  [Algebra R K] [Algebra R A] [Algebra R A'] [Algebra A A'] [Algebra K A']
  [IsScalarTower R A A'] [IsScalarTower R K A']
  [Module.Finite K A'] [_root_.IsReduced A']

/-- The original inclusion into the finite algebra gives the actual projection. -/
def projection : Spec (.of A) ⟶ Spec (.of (model R K A A')) :=
  Spec.map (CommRingCat.ofHom (model R K A A').val.toRingHom)

/-- The intermediate scheme retains its original base structural map. -/
def structureMap : Spec (.of (model R K A A')) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (model R K A A')))

instance projection_finite [Module.Finite R A] : IsFinite (projection R K A A') := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact (inferInstance : Module.Finite (model R K A A') A)

instance projection_surjective [Module.Finite R A] : Surjective (projection R K A A') := by
  have h : (model R K A A').val.toRingHom.Finite :=
    (inferInstance : Module.Finite (model R K A A') A)
  exact ⟨h.to_isIntegral.comap_surjective Subtype.val_injective⟩

instance structureMap_finite [IsNoetherianRing R] [Module.Finite R A] :
    IsFinite (structureMap R K A A') := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

@[reassoc (attr := simp)]
theorem projection_structureMap :
    projection R K A A' ≫ structureMap R K A A' =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [projection, structureMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (model R K A A').val.comp_algebraMap)

/-- The separable generic algebra is the actual generic fibre of the intermediate
scheme. Both legs are the original scalar maps. -/
theorem generic_isPullback (M : Submonoid R) [IsLocalization M K]
    [IsLocalization (M.map (algebraMap R A)) A'] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (model R K A A') (genericPart K A'))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (genericPart K A'))))
      (structureMap R K A A')
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : Algebra.IsPushout R (model R K A A') K (genericPart K A') :=
    genericMap_isPushout R K A A' M
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ..)

/-- The original source generic algebra is likewise the actual pullback over the
intermediate algebra, not a replacement chosen only up to field isomorphism. -/
theorem projection_generic_isPullback (M : Submonoid R) [IsLocalization M K]
    [IsLocalization (M.map (algebraMap R A)) A'] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      (Spec.map (CommRingCat.ofHom (genericPart K A').val.toRingHom))
      (projection R K A A')
      (Spec.map (CommRingCat.ofHom (algebraMap (model R K A A') (genericPart K A')))) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid A M) A' :=
    (inferInstance : IsLocalization (M.map (algebraMap R A)) A')
  have : IsLocalization (Algebra.algebraMapSubmonoid (model R K A A') M)
      (genericPart K A') := genericMap_isLocalization R K A A' M
  have : IsLocalization
      (Algebra.algebraMapSubmonoid A
        (Algebra.algebraMapSubmonoid (model R K A A') M)) A' := by
    change IsLocalization
      ((Algebra.algebraMapSubmonoid (model R K A A') M).map
        (model R K A A').val.toRingHom) A'
    infer_instance
  have : Algebra.IsPushout (model R K A A') A (genericPart K A') A' :=
    Algebra.isPushout_of_isLocalization
      (Algebra.algebraMapSubmonoid (model R K A A') M) (genericPart K A') A A'
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ..)

instance generic_structureMap_etale :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K (genericPart K A')))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The actual generic projection is radicial. -/
instance generic_projection_universallyInjective :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (genericPart K A').val.toRingHom)) := by
  apply ((tfae_universallyInjective _).out 2 1).mp
  intro L _ a b hab
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply genericPart_restriction_injective K A' L
  change (CommRingCat.ofHom (genericPart K A').val.toRingHom ≫ a).hom =
    (CommRingCat.ofHom (genericPart K A').val.toRingHom ≫ b).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  simpa only [Spec.map_comp] using hab

end AlgebraicGeometry.Scheme.FiniteGenericSubalgebra
