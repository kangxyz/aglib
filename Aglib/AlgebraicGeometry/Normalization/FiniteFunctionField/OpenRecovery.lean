/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField
public import Aglib.AlgebraicGeometry.FunctionField.Finite
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-! # Whole-open recovery for normal finite covers

The relative normalization of the original generic map recovers the entire
normal source over the specified open. Unlike finite-etale open recovery,
normality is a property of the source itself; ramification and inseparable
function-field extensions are allowed. No point of the source is deleted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteNormalOpen

section IntegralRecovery

variable {X V E : Scheme.{u}} [IsIntegral E]
  [∀ x : E, IsIntegrallyClosed (E.presheaf.stalk x)]
  (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (p : E ⟶ V) [IsIntegralHom p]

/-- The original generic map to the ambient scheme. -/
def genericMap : Spec E.functionField ⟶ X :=
  (E.fromSpecStalk (genericPoint E) ≫ p) ≫ j

instance : QuasiCompact (genericMap j p) := by
  unfold genericMap
  infer_instance

instance : QuasiSeparated (genericMap j p) := by
  unfold genericMap
  infer_instance

/-- Integral-factor invariance and normality recover the entire original source. -/
def originalNormalizationIso :
    (E.fromSpecStalk (genericPoint E) ≫ p).normalization ≅ E :=
  Hom.normalizationIntegralFactorIso (E.fromSpecStalk (genericPoint E)) p ≪≫
    asIso (E.fromSpecStalk (genericPoint E)).fromNormalization

@[reassoc]
theorem originalNormalizationIso_over :
    (originalNormalizationIso p).hom ≫ p =
      (E.fromSpecStalk (genericPoint E) ≫ p).fromNormalization :=
  Hom.normalizationIntegralFactorIso_hom_over _ _

/-- Normalization commutes with the actual open pullback square. -/
def normalizationPullbackIso :
    (E.fromSpecStalk (genericPoint E) ≫ p).normalization ≅
      pullback (genericMap j p).fromNormalization j := by
  let t := E.fromSpecStalk (genericPoint E) ≫ p
  have H : IsPullback (𝟙 _) t (genericMap j p) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]; rfl⟩
  exact Hom.normalizationSourceIso H.isoPullback t
      (pullback.snd (genericMap j p) j) H.isoPullback_hom_snd ≪≫
    asIso ((genericMap j p).normalizationPullback j)

omit [∀ x : E, IsIntegrallyClosed (E.presheaf.stalk x)] in
@[reassoc]
theorem normalizationPullbackIso_over :
    (normalizationPullbackIso j p).hom ≫ pullback.snd _ _ =
      (E.fromSpecStalk (genericPoint E) ≫ p).fromNormalization := by
  dsimp only [normalizationPullbackIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Hom.normalizationPullback_snd]
  exact Hom.normalizationSourceIso_hom_over _ _ _ _

/-- The whole source, not a further open subset, is the normalization pullback. -/
def iso : E ≅ pullback (genericMap j p).fromNormalization j :=
  (originalNormalizationIso p).symm ≪≫ normalizationPullbackIso j p

@[reassoc (attr := simp)]
theorem iso_hom_snd : (iso j p).hom ≫ pullback.snd _ _ = p := by
  apply (cancel_epi (originalNormalizationIso p).hom).mp
  simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact (normalizationPullbackIso_over j p).trans (originalNormalizationIso_over p).symm

/-- The unchanged source as an open subscheme of the relative normalization. -/
def inclusion : E ⟶ (genericMap j p).normalization :=
  (iso j p).hom ≫ pullback.fst _ _

@[reassoc (attr := simp)]
theorem inclusion_over :
    inclusion j p ≫ (genericMap j p).fromNormalization = p ≫ j := by
  simp only [inclusion, Category.assoc, pullback.condition, iso_hom_snd_assoc]

/-- The original finite map is exactly the pullback of the normalization map. -/
theorem isPullback : IsPullback (inclusion j p) p (genericMap j p).fromNormalization j :=
  IsPullback.of_iso_pullback ⟨inclusion_over j p⟩ (iso j p) rfl (iso_hom_snd j p)

instance : IsOpenImmersion (inclusion j p) :=
  MorphismProperty.of_isPullback (isPullback j p).flip inferInstance

end IntegralRecovery

section FiniteField

variable {X V E : Scheme.{u}} [IsIntegral E] [IsIntegral X] [IsIntegral V]
  (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (p : E ⟶ V) [IsFinite p] [IsDominant p]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The field action is the actual generic-stalk map of the original composite. -/
@[instance_reducible]
def functionFieldAlgebra : Algebra X.functionField E.functionField :=
  (functionFieldMap (p ≫ j)).toAlgebra

omit [QuasiCompact j] in
private theorem functionField_finite :
    let := functionFieldAlgebra j p
    Module.Finite X.functionField E.functionField := by
  change (functionFieldMap (p ≫ j)).Finite
  rw [functionFieldMap_comp]
  exact (functionFieldMap_finite p).comp
    (RingHom.Finite.of_surjective _ (FunctionField.fieldEquiv j).surjective)

omit [QuasiCompact j] [IsFinite p] in
/-- The unchanged generic map agrees with the finite-field normalization input. -/
theorem genericMap_eq_functionField :
    let := functionFieldAlgebra j p
    genericMap j p = FiniteFunctionField.genericMap X E.functionField := by
  unfold genericMap FiniteFunctionField.genericMap FiniteFunctionField.genericCover
  exact (Category.assoc _ p j).trans (fromSpecStalk_genericPoint_naturality (p ≫ j))

/-- The actual ambient relative normalization is normal, without an etale or
separability premise on the finite projection. -/
theorem normalization_normalStalks : NormalStalks (genericMap j p).normalization := by
  let := functionFieldAlgebra j p
  let : Module.Finite X.functionField E.functionField := functionField_finite j p
  have h := FiniteFunctionField.normalization_normalStalks X E.functionField
  change NormalStalks (FiniteFunctionField.genericMap X E.functionField).normalization at h
  simpa only [← genericMap_eq_functionField j p] using h

/-- Nagata original base-chart rings make the very same normalization finite. -/
theorem fromNormalization_isFinite
    (hNagata : ∀ W : X.affineOpens, Nonempty W.1 → IsNagataRing.{u, 0} Γ(X, W.1)) :
    IsFinite (genericMap j p).fromNormalization := by
  let := functionFieldAlgebra j p
  let : Module.Finite X.functionField E.functionField := functionField_finite j p
  let f := FiniteFunctionField.genericMap X E.functionField
  let : IsFinite f.fromNormalization :=
    FiniteFunctionField.fromNormalization_isFinite X E.functionField hNagata
  have hmap : (Iso.refl (Spec E.functionField)).hom ≫ f = genericMap j p := by
    simpa only [Iso.refl_hom, Category.id_comp] using
      (genericMap_eq_functionField j p).symm
  let e := Hom.normalizationSourceIso (Iso.refl _) (genericMap j p) f hmap
  have he : e.hom ≫ f.fromNormalization = (genericMap j p).fromNormalization :=
    Hom.normalizationSourceIso_hom_over _ _ _ _
  have hfinite : IsFinite (e.hom ≫ f.fromNormalization) := inferInstance
  exact he ▸ hfinite

end FiniteField

end AlgebraicGeometry.Scheme.FiniteNormalOpen
