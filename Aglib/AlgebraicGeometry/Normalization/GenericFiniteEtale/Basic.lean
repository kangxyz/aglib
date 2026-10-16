/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic
public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Generic fibres of relative normalizations of finite etale covers

Starting with the given finite etale scheme over the actual function field, use Mathlib
relative normalization of its composite map to the base. Integral-closure charts recover
the original scheme as the literal generic pullback. Only integrality of the base is used;
normality, local Noetherianity, dimensions and nonemptiness of the cover are not assumed.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericNormalization.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`d4e8c371f13557079b4051530de44bc742dcd1d9c6850e9a5788477b95c26601`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (C : Scheme.FiniteEtale (Spec X.functionField))

/-- The canonical comparison into the LITERAL generic pullback of the model. -/
def comparison : C.obj.left ⟶ pullback ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))).fromNormalization) (X.fromSpecStalk (genericPoint X)) :=
  pullback.lift ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).toNormalization) C.obj.hom
      (Scheme.Hom.toNormalization_fromNormalization (C.obj.hom ≫ (X.fromSpecStalk (genericPoint
      X))))

/-- The first projection of the generic comparison is the canonical normalization map. -/
@[reassoc (attr := simp)] theorem comparison_fst :
    comparison X C ≫ pullback.fst _ _ = (C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).toNormalization := pullback.lift_fst ..

/-- The second projection of the generic comparison is the original function-field structure map. -/
@[reassoc (attr := simp)] theorem comparison_snd :
    comparison X C ≫ pullback.snd _ _ = C.obj.hom := pullback.lift_snd ..

section AffineChart

variable (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

/-- Every nonempty open of the base pulls back to the whole original generic scheme. -/
theorem preimage_genericMap : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U = ⊤ := by
  simp only [Scheme.Hom.comp_preimage, fromSpecStalk_genericPoint_preimage]
  simp

/-- The original generic algebra on this chart is literally its sections
on an inverse image equal to the entire original generic scheme. -/
def chartOriginalSectionsIso :
    Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) ≅ Γ(C.obj.left, ⊤) :=
  C.obj.left.presheaf.mapIso (eqToIso (preimage_genericMap X C U).symm).op

/-- The actual field scalar map on the original chart algebra. -/
def chartFunctionFieldMap : X.functionField ⟶ Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk
    (genericPoint X))) ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso X.functionField).inv ≫
    C.obj.hom.appLE ⊤ ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) (by simp)

/-- The chart function-field algebra uses the original scheme structural map on sections. -/
instance instChartFunctionFieldAlgebra : Algebra X.functionField (Γ(C.obj.left, (C.obj.hom ≫
    (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)) :=
  (chartFunctionFieldMap X C U).hom.toAlgebra

/-- The chart base algebra uses the composite map to the base on sections. -/
instance instChartBaseAlgebra : Algebra Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk
    (genericPoint X))) ⁻¹ᵁ U)) :=
  ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).app U).hom.toAlgebra

/-- The generic-inclusion section map agrees with the actual germ-to-function-field map. -/
private theorem genericAppLE_square :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤ (by rw [fromSpecStalk_genericPoint_preimage]) =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso X.functionField).hom).mp
  simp only [Scheme.Hom.appLE, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : (homOfLE (show ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U from
      (fromSpecStalk_genericPoint_preimage X U).symm.le)).op =
      (eqToIso (fromSpecStalk_genericPoint_preimage X U).symm).op.hom := Subsingleton.elim _ _
  rw [he]
  exact fromSpecStalk_genericPoint_app_functionFieldSectionsIso X U

/-- The chosen chart algebra structures form the actual base/function-field scalar tower. -/
instance instChartScalarTower :
    IsScalarTower Γ(X, U) X.functionField (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))) ⁻¹ᵁ U)) := by
  apply IsScalarTower.of_algebraMap_eq'
  change ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).app U).hom =
    (chartFunctionFieldMap X C U).hom.comp (X.germToFunctionField U).hom
  change ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).app U).hom =
    (X.germToFunctionField U ≫ chartFunctionFieldMap X C U).hom
  rw [chartFunctionFieldMap, ← Category.assoc, ← genericAppLE_square X U]
  rw [Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.app_eq_appLE]

/-- The original chart algebra is finite over the actual function field. -/
instance instChartAlgebraFinite : Module.Finite X.functionField (Γ(C.obj.left, (C.obj.hom ≫
    (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)) := by
  have hres : Function.Surjective
      (C.obj.left.presheaf.map (homOfLE (show (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U
          ≤ ⊤ from le_top)).op).hom := by
    haveI : IsIso (C.obj.left.presheaf.map
      (homOfLE (show (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U ≤ ⊤ from le_top)).op) :=
          by
      have he : homOfLE (show (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U ≤ ⊤ from
          le_top) =
          eqToHom (preimage_genericMap X C U) := Subsingleton.elim _ _
      rw [he]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hf : (chartFunctionFieldMap X C U).hom.Finite := by
    dsimp [chartFunctionFieldMap]
    rw [Scheme.Hom.appLE]
    exact (RingHom.Finite.of_surjective _ hres).comp
      (C.obj.hom.finite_appTop.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).inv).2))
  exact hf

/-- The original chart algebra is etale over the actual function field. -/
instance instChartAlgebraEtale : Algebra.Etale X.functionField (Γ(C.obj.left, (C.obj.hom ≫
    (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)) := by
  letI : IsAffine C.obj.left := isAffine_of_isAffineHom C.obj.hom
  have hV : IsAffineOpen ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) := by
    rw [preimage_genericMap X C U]
    exact isAffineOpen_top _
  change (chartFunctionFieldMap X C U).hom.Etale
  simpa only [chartFunctionFieldMap, CommRingCat.hom_comp] using
    RingHom.Etale.stableUnderComposition (Scheme.ΓSpecIso X.functionField).inv.hom
      (C.obj.hom.appLE ⊤ ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) (by simp)).hom
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).inv))
      (C.obj.hom.etale_appLE (isAffineOpen_top (Spec X.functionField)) hV (by simp))

include hU in
/-- The original algebra forms the canonical algebraic generic pullback
square of its actual integral closure. -/
private theorem chartSpec_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap
        (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
            U))) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)))))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫
          (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
            U))))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) X.functionField))) := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  letI := _root_.integralClosure.isLocalization Γ(X, U) X.functionField (Γ(C.obj.left, (C.obj.hom ≫
      (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U))
  haveI : Algebra.IsPushout Γ(X, U)
      (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
          U))) X.functionField
        (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)) :=
    Algebra.isPushout_of_isLocalization Γ(X, U)⁰ X.functionField
      (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
          U))) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U))
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ..)

omit [Nonempty U] in
/-- The actual normalization chart is a pullback of the original affine
open in X; this uses the constructed normalization's actual gluing map. -/
theorem isPullback_chart :
    IsPullback ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalizationOpenCover.f ⟨U, hU⟩)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
            U))))))
      ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization) hU.fromSpec := by
  dsimp only [Scheme.Hom.normalizationOpenCover]
  apply (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
      X))).normalizationGlueData.isPullback_natTrans_ι_toBase
    ⟨U, hU⟩).flip).of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec (Iso.refl _)
  · simp
  · simp [Scheme.Hom.normalizationGlueData, Scheme.AffineZariskiSite.relativeGluingData,
      Scheme.Hom.normalizationDiagramMap]
  · simp
    rfl
  · simp [IsAffineOpen.isoSpec_hom]

/-- The inclusion of the original inverse image of a nonempty base open is an isomorphism. -/
instance originalPreimage_iota_isIso : IsIso ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))) ⁻¹ᵁ U).ι := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro x
  exact ⟨⟨x, by rw [preimage_genericMap X C U]; trivial⟩, rfl⟩

/-- Canonical identification of the ORIGINAL generic scheme with its
actual chart sections; it is built from restriction to the entire scheme. -/
def localOriginalIso : C.obj.left ≅ Spec (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))) ⁻¹ᵁ U)) := by
  letI : IsAffine C.obj.left := isAffine_of_isAffineHom C.obj.hom
  have hV : IsAffineOpen ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) := by
    rw [preimage_genericMap X C U]
    exact isAffineOpen_top _
  exact (asIso ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).ι).symm ≪≫
    hV.isoSpec

/-- The local affine identification respects the original function-field structural morphism. -/
theorem localOriginalIso_structure :
    (localOriginalIso X C U).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫
          (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)))) =
        C.obj.hom := by
  letI : IsAffine C.obj.left := isAffine_of_isAffineHom C.obj.hom
  have hV : IsAffineOpen ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) := by
    rw [preimage_genericMap X C U]
    exact isAffineOpen_top _
  apply (cancel_epi ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).ι).mp
  dsimp [localOriginalIso]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  change ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).toSpecΓ ≫ Spec.map
      (chartFunctionFieldMap X C U) =
    ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).ι ≫ C.obj.hom
  rw [chartFunctionFieldMap, Spec.map_comp]
  simpa only [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Category.assoc,
    IsAffineOpen.toSpecΓ_fromSpec_assoc] using
    congrArg (fun f => ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).toSpecΓ ≫ f)
      (IsAffineOpen.SpecMap_appLE_fromSpec C.obj.hom
        (isAffineOpen_top (Spec X.functionField)) hV (by simp))

/-- The local affine identification respects the canonical map to relative normalization. -/
theorem localOriginalIso_normalization :
    (localOriginalIso X C U).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap
        (integralClosure Γ(X, U) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
            U))) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)))) ≫
        (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalizationOpenCover.f ⟨U, hU⟩ =
            (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).toNormalization := by
  letI : IsAffine C.obj.left := isAffine_of_isAffineHom C.obj.hom
  apply (cancel_epi ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U).ι).mp
  dsimp [localOriginalIso]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).ι_toNormalization ⟨U, hU⟩).symm

end AffineChart

/-- The normalization square of the ORIGINAL generic cover is an actual
pullback square, proved from local integral-closure localization and the
normalization chart squares. Generic inclusion is never assumed smooth. -/
theorem isPullback_generic :
    IsPullback ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).toNormalization) C.obj.hom
        ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization) (X.fromSpecStalk
        (genericPoint X)) := by
  let x : X := Classical.choice inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hfirst : IsPullback (localOriginalIso X C U).hom C.obj.hom
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫
          (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)))))
      (𝟙 (Spec X.functionField)) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using
      (localOriginalIso_structure X C U)⟩
  have htotal := hfirst.paste_horiz
    ((chartSpec_isPullback X C U hU).paste_horiz (isPullback_chart X C U hU))
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) X.functionField)) ≫
      hU.fromSpec = (X.fromSpecStalk (genericPoint X)) :=
    hU.fromSpecStalk_eq_fromSpecStalk
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))
  rw [localOriginalIso_normalization X C U hU, hbase, Category.id_comp] at htotal
  exact htotal

section AffineChart

variable (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

end AffineChart

/-- The canonical literal generic comparison is an actual scheme isomorphism,
not a supplied normalization-fibre dictionary. -/
instance instIsIsoComparison : IsIso (comparison X C) := by
  let h := isPullback_generic X C
  have he : comparison X C = h.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [comparison_fst, IsPullback.isoPullback_hom_fst]
    · simp only [comparison_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

section AffineChart

variable (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]

end AffineChart

/-- The identification is over the original actual function field. -/
def genericFiberOverIso :
    C.obj ≅ Over.mk (pullback.snd ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).fromNormalization) (X.fromSpecStalk (genericPoint X))) :=
  Over.isoMk (asIso (comparison X C)) (comparison_snd X C)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
