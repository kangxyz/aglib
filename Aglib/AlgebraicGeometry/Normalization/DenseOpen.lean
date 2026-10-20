/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Normalization.Relative

/-!
# Relative normalization of a dense open in a normal integral scheme

On each nonempty affine chart, the sections of the dense open embed in the same
function field. Integral closedness of the affine base therefore makes its actual
integral closure equal to the base. Mathlib's `fromNormalization_app` identifies
this map with the structural map of the relative normalization.

The universal predicate is the exact interface in
`R5Lab/Aglib/AlgebraicGeometry/Normalization/Relative.lean`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`650965d46d326d81575d6457010fa1de4322761ba02e99750e4ccb68df65bbbc`.
The supplier is proved here without a Noetherian or dimension hypothesis.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Every qcqs dominant open immersion into a normal integral scheme has trivial
relative normalization, for arbitrary schemes in the same universe. -/
def DenseOpenNormalNormalization : Prop :=
  ∀ (X Y : Scheme.{u}) (j : X ⟶ Y) [QuasiCompact j] [QuasiSeparated j],
    IsIntegral Y → NormalStalks Y → IsOpenImmersion j → IsDominant j →
      IsIso j.fromNormalization

namespace Hom

variable {X Y : Scheme.{u}} (j : X ⟶ Y)

/-- On a nonempty affine chart, the literal integral closure in the sections of
the dense open has no extra elements. The comparison is its actual algebra map. -/
theorem integralClosure_algebraMap_bijective_of_isOpenImmersion
    [IsIntegral Y] [IsOpenImmersion j] [IsDominant j]
    (hY : NormalStalks Y) (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (j.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, j ⁻¹ᵁ U))) := by
  let := (j.app U).hom.toAlgebra
  have : Nonempty X := j.denseRange.nonempty
  have : IsIntegral X := isIntegral_of_isOpenImmersion j
  have : Nonempty (j ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := j.denseRange.exists_mem_open U.isOpen
      (by simpa using (inferInstance : Nonempty U))
    exact ⟨⟨x, hx⟩⟩
  let (y : Y) : IsIntegrallyClosed (Y.presheaf.stalk y) := (hY y).2
  have : IsIntegrallyClosed Γ(Y, U) := isIntegrallyClosed_sections_of_isAffineOpen Y U hU
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have hgerm : Y.germToFunctionField U ≫ CommRingCat.ofHom (functionFieldMap j) =
      j.app U ≫ X.germToFunctionField (j ⁻¹ᵁ U) := by
    change Y.presheaf.germ U _ _ ≫ (Y.presheaf.stalkSpecializes _ ≫ j.stalkMap _) = _
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, germ_stalkMap]
  let e : Γ(X, j ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField :=
    { toRingHom := (FunctionField.fieldEquiv j).symm.toRingHom.comp
        (X.germToFunctionField (j ⁻¹ᵁ U)).hom
      commutes' r := by
        change (FunctionField.fieldEquiv j).symm
          (X.germToFunctionField (j ⁻¹ᵁ U) (j.app U r)) =
            Y.germToFunctionField U r
        apply (FunctionField.fieldEquiv j).injective
        rw [RingEquiv.apply_symm_apply]
        exact congr($(hgerm) r).symm }
  have he : Function.Injective e :=
    (FunctionField.fieldEquiv j).symm.injective.comp
      (X.germToFunctionField_injective (j ⁻¹ᵁ U))
  constructor
  · intro r s hrs
    apply IsFractionRing.injective Γ(Y, U) Y.functionField
    have h := congrArg (fun z => e z.val) hrs
    simpa only [Subalgebra.coe_algebraMap, e.commutes] using h
  · intro z
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (z.property.map e)
    refine ⟨r, Subtype.ext (he ?_)⟩
    rw [Subalgebra.coe_algebraMap, e.commutes]
    exact hr

/-- The structural map of the actual relative normalization is an isomorphism.
Dominance supplies nonemptiness; no normality or integrality of the source is assumed. -/
theorem isIso_fromNormalization_of_isOpenImmersion
    [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
    [IsOpenImmersion j] [IsDominant j] (hY : NormalStalks Y) :
    IsIso j.fromNormalization := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms _) fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  let := (j.app U).hom.toAlgebra
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U)
      (integralClosure Γ(Y, U) Γ(X, j ⁻¹ᵁ U)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (j.integralClosure_algebraMap_bijective_of_isOpenImmersion hY U hU)
  have happ : IsIso (j.fromNormalization.app U) := by
    rw [fromNormalization_app _ hU]
    infer_instance
  exact ⟨U, hyU, (isIso_morphismRestrict_iff_isIso_app _ hU).mpr happ⟩

/-- The isomorphism uses the actual `fromNormalization` as its forward map. -/
def denseOpenNormalizationIso [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
    [IsOpenImmersion j] [IsDominant j] (hY : NormalStalks Y) : j.normalization ≅ Y := by
  have := j.isIso_fromNormalization_of_isOpenImmersion hY
  exact asIso j.fromNormalization

@[simp] theorem denseOpenNormalizationIso_hom
    [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
    [IsOpenImmersion j] [IsDominant j] (hY : NormalStalks Y) :
    (j.denseOpenNormalizationIso hY).hom = j.fromNormalization := rfl

/-- The original open immersion is the canonical factorization through its normalization. -/
@[reassoc (attr := simp)] theorem toNormalization_denseOpenNormalizationIso_hom
    [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
    [IsOpenImmersion j] [IsDominant j] (hY : NormalStalks Y) :
    j.toNormalization ≫ (j.denseOpenNormalizationIso hY).hom = j :=
  j.toNormalization_fromNormalization

/-- The inverse triangle identifies the original normalization inclusion literally. -/
@[reassoc (attr := simp)] theorem comp_denseOpenNormalizationIso_inv
    [QuasiCompact j] [QuasiSeparated j] [IsIntegral Y]
    [IsOpenImmersion j] [IsDominant j] (hY : NormalStalks Y) :
    j ≫ (j.denseOpenNormalizationIso hY).inv = j.toNormalization := by
  calc
    _ = (j.toNormalization ≫ (j.denseOpenNormalizationIso hY).hom) ≫
        (j.denseOpenNormalizationIso hY).inv :=
      congrArg (fun f => f ≫ (j.denseOpenNormalizationIso hY).inv)
        (j.toNormalization_denseOpenNormalizationIso_hom hY).symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Hom

/-- A proved term of the original universal dense-open normalization interface. -/
theorem denseOpenNormalNormalization : DenseOpenNormalNormalization.{u} := by
  intro X Y j _ _ _ hY _ _
  exact j.isIso_fromNormalization_of_isOpenImmersion hY

end AlgebraicGeometry.Scheme
