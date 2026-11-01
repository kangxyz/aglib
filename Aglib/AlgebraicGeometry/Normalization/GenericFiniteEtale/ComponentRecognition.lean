/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Recognition of the original finite normal component

A finite integral normal scheme with the original covering scheme as a dense
open is the native normalization in that cover's original generic source.
The constructed comparison retains the actual base, generic and open maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left]

section Inclusion

variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

omit [IsIntegral Y.obj.left] in
/-- The original open-recovery inclusion retains the entire generic source map. -/
@[reassoc] theorem genericToCover_inclusion :
    genericToCover j Y.obj.hom ≫ inclusion j Y.obj.hom =
      (genericMap j Y.obj.hom).toNormalization := by
  let t := genericToCover j Y.obj.hom ≫ Y.obj.hom
  have ht : genericToCover j Y.obj.hom ≫ (originalNormalizationIso j Y.obj.hom).inv =
      t.toNormalization := by
    apply (cancel_mono (originalNormalizationIso j Y.obj.hom).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [originalNormalizationIso, Iso.trans_hom, asIso_hom]
    change _ = t.toNormalization ≫
      (Hom.normalizationIntegralFactorIso (genericToCover j Y.obj.hom) Y.obj.hom).hom ≫
        (genericToCover j Y.obj.hom).fromNormalization
    dsimp only [t, Hom.normalizationIntegralFactorIso]
    rw [Hom.toNormalization_normalizationDesc_assoc, Hom.toNormalization_fromNormalization]
  dsimp only [inclusion, iso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, ht]
  dsimp only [normalizationPullbackIso, Iso.trans_hom, asIso_hom]
  rw [Hom.normalizationSourceIso_hom_generic_assoc]
  simp only [Category.assoc]
  rw [Hom.toNormalization_normalizationPullback_fst]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]

end Inclusion

variable {C : Scheme.{u}} [IsIntegral C] (hC : NormalStalks C)
  (g : C ⟶ X) [IsFinite g] (b : Y.obj.left ⟶ C) [IsOpenImmersion b]
  (hb : b ≫ g = Y.obj.hom ≫ j)

omit [IsIntegral Y.obj.left] [IsIntegral C] [IsFinite g] [IsOpenImmersion b] in
include hb in
/-- The actual generic source factors through the supplied original component. -/
theorem genericMap_eq_component :
    genericMap j Y.obj.hom = (genericToCover j Y.obj.hom ≫ b) ≫ g := by
  rw [genericMap_eq]
  simp only [Category.assoc, hb]

/-- The same original generic source is the spectrum of the component's
function field, through the original open function-field map. -/
def componentGenericSourceIso :
    (genericCover j Y.obj.hom).obj.left ≅ Spec C.functionField := by
  let : IsDominant b := Scheme.isDominant_of_isOpenImmersion b
  let : IsIso (CommRingCat.ofHom (functionFieldMap b)) := FunctionField.fieldMap_isIso b
  exact (originalFieldSpectrumIso j Y).symm ≪≫
    asIso (Spec.map (CommRingCat.ofHom (functionFieldMap b)))

@[reassoc] theorem componentGenericSourceIso_hom_generic :
    (componentGenericSourceIso j Y b).hom ≫ C.fromSpecStalk (genericPoint C) =
      genericToCover j Y.obj.hom ≫ b := by
  let : IsDominant b := Scheme.isDominant_of_isOpenImmersion b
  apply (cancel_epi (originalFieldSpectrumIso j Y).hom).mp
  simp only [componentGenericSourceIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    originalFieldSpectrumIso_hom_toCover]
  exact (fromSpecStalk_genericPoint_naturality b).symm

instance componentGeneric_quasiCompact : QuasiCompact (genericToCover j Y.obj.hom ≫ b) := by
  rw [← componentGenericSourceIso_hom_generic j Y b]
  infer_instance

include hC in
/-- The actual generic-source map into the normal component has trivial
normalization, derived from the original open function-field isomorphism. -/
theorem componentGenericFromNormalization_isIso :
    IsIso (genericToCover j Y.obj.hom ≫ b).fromNormalization := by
  let : ∀ c : C, IsIntegrallyClosed (C.presheaf.stalk c) := fun c => (hC c).2
  let n := Hom.normalizationSourceIso (componentGenericSourceIso j Y b)
    (genericToCover j Y.obj.hom ≫ b) (C.fromSpecStalk (genericPoint C))
    (componentGenericSourceIso_hom_generic j Y b)
  have hn : n.hom ≫ (C.fromSpecStalk (genericPoint C)).fromNormalization =
      (genericToCover j Y.obj.hom ≫ b).fromNormalization :=
    Hom.normalizationSourceIso_hom_over ..
  rw [← hn]
  infer_instance

/-- Recognition uses the actual universal normalization map to the original
component, not an assumed comparison or a replacement connected model. -/
def componentRecognitionIso : (genericMap j Y.obj.hom).normalization ≅ C := by
  let := componentGenericFromNormalization_isIso j Y hC b
  let h := genericMap_eq_component j Y g b hb
  let := Hom.normalizationDesc_isIso (genericMap j Y.obj.hom)
    (genericToCover j Y.obj.hom ≫ b) g h
  exact asIso ((genericMap j Y.obj.hom).normalizationDesc
    (genericToCover j Y.obj.hom ≫ b) g h)

@[reassoc (attr := simp)] theorem componentRecognitionIso_hom_over :
    (componentRecognitionIso j Y hC g b hb).hom ≫ g =
      (genericMap j Y.obj.hom).fromNormalization :=
  Hom.normalizationDesc_comp _ _ _ (genericMap_eq_component j Y g b hb)

@[reassoc (attr := simp)] theorem componentRecognitionIso_hom_generic :
    (genericMap j Y.obj.hom).toNormalization ≫ (componentRecognitionIso j Y hC g b hb).hom =
      genericToCover j Y.obj.hom ≫ b :=
  Hom.toNormalization_normalizationDesc _ _ _ (genericMap_eq_component j Y g b hb)

/-- The original covering-source inclusion is retained on the nose. -/
@[reassoc (attr := simp)] theorem inclusion_componentRecognitionIso_hom
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] :
    inclusion j Y.obj.hom ≫ (componentRecognitionIso j Y hC g b hb).hom = b := by
  apply ext_of_isDominant_of_isSeparated g
    (by rw [Category.assoc, componentRecognitionIso_hom_over, inclusion_over, hb])
    (Y.obj.left.fromSpecStalk (genericPoint Y.obj.left))
  rw [← originalFieldSpectrumIso_hom_toCover j Y]
  simp only [Category.assoc, genericToCover_inclusion_assoc,
    componentRecognitionIso_hom_generic]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
