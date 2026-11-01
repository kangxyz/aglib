/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecovery
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericGalois
public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # The original generic tensor of an open-base-changed integral cover

The original function fields and actual generic-stalk maps determine the tensor
comparison. Open-field transport, the canonical generic fibre of the unchanged
finite cover, and native tensor pullbacks construct the isomorphism used by open
recovery. No generic-cover comparison or replacement field is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

section TensorFactory

variable (K F L : Type u) [CommRing K] [CommRing F] [CommRing L]
  [Algebra K F] [Algebra K L]
  {X U E : Scheme.{u}} (p : E ⟶ X) (g : U ⟶ X)
  (γK : Spec (.of K) ⟶ X) (γF : Spec (.of F) ⟶ U)
  (e : Spec (.of L) ≅ pullback p γK)
  (he : e.hom ≫ pullback.snd p γK = Spec.algebraMap K L)
  (hγ : γF ≫ g = Spec.algebraMap K F ≫ γK)

/-- Tensor spectra compute the actual iterated pullback with its supplied original square. -/
def tensorPullbackIso :
    Spec (.of (F ⊗[K] L)) ≅ pullback γF (pullback.snd p g) :=
  (pullbackSpecIso K F L).symm ≪≫
    pullbackSymmetry _ _ ≪≫
    asIso (pullback.map (Spec.algebraMap K L) (Spec.algebraMap K F)
      (pullback.snd p γK) (Spec.algebraMap K F) e.hom (𝟙 _) (𝟙 _)
      (by simpa using he.symm) (by simp)) ≪≫
    pullbackLeftPullbackSndIso p γK (Spec.algebraMap K F) ≪≫
    pullback.congrHom rfl hγ.symm ≪≫
    (pullbackLeftPullbackSndIso p g γF).symm ≪≫
    pullbackSymmetry _ _

private theorem tensorPullbackIso_hom_fst :
    (tensorPullbackIso K F L p g γK γF e he hγ).hom ≫ pullback.fst _ _ =
      Spec.algebraMap F (F ⊗[K] L) := by
  simp only [tensorPullbackIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_inv_snd_snd,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd,
    pullbackSpecIso_inv_fst']

private theorem tensorPullbackIso_hom_snd_fst :
    (tensorPullbackIso K F L p g γK γF e he hγ).hom ≫
        pullback.snd _ _ ≫ pullback.fst p g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toRingHom) ≫
          e.hom ≫ pullback.fst p γK := by
  simp only [tensorPullbackIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
    pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  rfl

variable (H : Type u) [CommRing H] (γH : Spec (.of H) ⟶ U)
  (eF : Spec (.of F) ≅ Spec (.of H))
  (hF : (eF.hom ≫ γH) ≫ g = Spec.algebraMap K F ≫ γK)

/-- The same tensor comparison after the original generic-spectrum reindexing. -/
def tensorPullbackIsoReindex :
    Spec (.of (F ⊗[K] L)) ≅ pullback γH (pullback.snd p g) :=
  tensorPullbackIso K F L p g γK (eF.hom ≫ γH) e he hF ≪≫
    asIso (pullback.map (eF.hom ≫ γH) (pullback.snd p g) γH (pullback.snd p g)
      eF.hom (𝟙 _) (𝟙 _) (by simp) (by simp))

private theorem tensorPullbackIsoReindex_hom_fst :
    (tensorPullbackIsoReindex K F L p g γK e he H γH eF hF).hom ≫
        pullback.fst _ _ = Spec.algebraMap F (F ⊗[K] L) ≫ eF.hom := by
  simp only [tensorPullbackIsoReindex, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst]
  rw [← Category.assoc, tensorPullbackIso_hom_fst]

/-- The reindexed tensor comparison retains the whole original source map. -/
theorem tensorPullbackIsoReindex_hom_source (γL : Spec (.of L) ⟶ E)
    (heL : e.hom ≫ pullback.fst p γK = γL) :
    (tensorPullbackIsoReindex K F L p g γK e he H γH eF hF).hom ≫
        pullback.snd _ _ ≫ pullback.fst p g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toRingHom) ≫ γL := by
  simp only [tensorPullbackIsoReindex, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, Category.id_comp]
  rw [tensorPullbackIso_hom_snd_fst, heL]

/-- The reindexed tensor comparison retains the whole original ambient-base map. -/
theorem tensorPullbackIsoReindex_hom_base {Z : Scheme.{u}} (j : U ⟶ Z)
    (δF : Spec (.of F) ⟶ Z) (hδ : (eF.hom ≫ γH) ≫ j = δF) :
    (tensorPullbackIsoReindex K F L p g γK e he H γH eF hF).hom ≫
        (pullback.snd _ _ ≫ pullback.snd p g) ≫ j =
      Spec.algebraMap F (F ⊗[K] L) ≫ δF := by
  rw [← pullback.condition, ← Category.assoc, ← Category.assoc,
    tensorPullbackIsoReindex_hom_fst]
  simpa only [Category.assoc] using
    congrArg (fun q => Spec.algebraMap F (F ⊗[K] L) ≫ q) hδ

end TensorFactory

variable {X X' U : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsIntegral U]
  (j : U ⟶ X') [IsOpenImmersion j] (g : U ⟶ X) [IsDominant g]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The actual coefficient-field map through the original common open.
Only the open immersion's existing field equivalence is inverted. -/
def baseChangeFieldHom : X.functionField →+* X'.functionField :=
  (FunctionField.fieldEquiv j).symm.toRingHom.comp (functionFieldMap g)

/-- The coefficient action is the original generic-stalk map transported
through the original open immersion. -/
@[instance_reducible] def baseChangeFieldAlgebra : Algebra X.functionField X'.functionField :=
  (baseChangeFieldHom j g).toAlgebra


/-- The field square retains the actual original map, rather than an arbitrary embedding. -/
@[simp] theorem baseChangeFieldHom_open (x : X.functionField) :
    FunctionField.fieldEquiv j (baseChangeFieldHom j g x) = functionFieldMap g x :=
  (FunctionField.fieldEquiv j).apply_symm_apply _

/-- The coefficient embedding makes the original function-field square commute. -/
theorem baseChangeFieldHom_comp :
    (functionFieldMap j).comp (baseChangeFieldHom j g) = functionFieldMap g :=
  RingHom.ext (baseChangeFieldHom_open j g)

/-- The original open immersion identifies the two actual generic spectra. -/
def openGenericIso : Spec X'.functionField ≅ Spec U.functionField :=
  Scheme.Spec.mapIso (FunctionField.fieldEquiv j).symm.toCommRingCatIso.op

/-- The ambient generic point factors through the original open. -/
def openGenericMap : Spec X'.functionField ⟶ U :=
  (openGenericIso j).hom ≫ U.fromSpecStalk (genericPoint U)

private theorem openGenericMap_over :
    openGenericMap j ≫ j = X'.fromSpecStalk (genericPoint X') := by
  rw [openGenericMap, Category.assoc, FunctionField.fieldEquiv_generic_triangle j]
  change (openGenericIso j).hom ≫ (openGenericIso j).inv ≫ _ = _
  simp

/-- The original coefficient embedding gives the generic square. -/
theorem openGenericMap_generic :
    letI := baseChangeFieldAlgebra j g
    openGenericMap j ≫ g =
      Spec.algebraMap X.functionField X'.functionField ≫ X.fromSpecStalk (genericPoint X) := by
  let := baseChangeFieldAlgebra j g
  rw [openGenericMap, Category.assoc, fromSpecStalk_genericPoint_naturality g]
  change Spec.map (CommRingCat.ofHom (FunctionField.fieldEquiv j).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (functionFieldMap g)) ≫ _ = _
  rw [← Spec.map_comp_assoc]
  rfl

variable (Y : FiniteEtale X) [IsIntegral Y.obj.left]

@[instance_reducible] local instance coveringFieldAlgebra :
    Algebra X.functionField Y.obj.left.functionField := GenericGalois.algebra Y
local instance : IsDominant Y.obj.hom := GenericGalois.dominant Y

/-- The original generic-fibre lift as its native spectrum isomorphism. -/
def originalGenericFibreIso :
    Spec Y.obj.left.functionField ≅ pullback Y.obj.hom (X.fromSpecStalk (genericPoint X)) :=
  @asIso Scheme _ _ _ (genericFibreMap Y.obj.hom) (genericFibreMap_isIso Y.obj.hom)

/-- The original generic-fibre isomorphism retains the original coefficient map. -/
theorem originalGenericFibreIso_hom_snd :
    (originalGenericFibreIso Y).hom ≫ pullback.snd _ _ =
      Spec.algebraMap X.functionField Y.obj.left.functionField :=
  pullback.lift_snd _ _ _

/-- The original generic-fibre isomorphism retains the original generic-point map. -/
theorem originalGenericFibreIso_hom_fst :
    (originalGenericFibreIso Y).hom ≫ pullback.fst _ _ =
      Y.obj.left.fromSpecStalk (genericPoint Y.obj.left) :=
  pullback.lift_fst _ _ _

/-- The original tensor spectrum identifies the actual generic cover of the
actual pulled-back cover. The original covering field is not replaced. -/
def baseChangeFieldSpectrumIso :
    letI := baseChangeFieldAlgebra j g
    Spec (.of (X'.functionField ⊗[X.functionField] Y.obj.left.functionField)) ≅
      (genericCover j ((baseChange g).obj Y).obj.hom).obj.left := by
  letI := baseChangeFieldAlgebra j g
  exact @tensorPullbackIsoReindex X.functionField X'.functionField Y.obj.left.functionField
    inferInstance inferInstance inferInstance (baseChangeFieldAlgebra j g)
    (GenericGalois.algebra Y) X U Y.obj.left Y.obj.hom g (X.fromSpecStalk (genericPoint X))
    (originalGenericFibreIso Y) (originalGenericFibreIso_hom_snd Y)
    U.functionField inferInstance (U.fromSpecStalk (genericPoint U)) (openGenericIso j)
    (openGenericMap_generic j g)

/-- The comparison retains the original generic map into the ambient scheme. -/
@[reassoc] theorem baseChangeFieldSpectrumIso_hom_genericMap :
    letI := baseChangeFieldAlgebra j g
    (baseChangeFieldSpectrumIso j g Y).hom ≫
      genericMap j ((baseChange g).obj Y).obj.hom =
        Spec.algebraMap X'.functionField
          (X'.functionField ⊗[X.functionField] Y.obj.left.functionField) ≫
            X'.fromSpecStalk (genericPoint X') := by
  let := baseChangeFieldAlgebra j g
  rw [genericMap_eq]
  exact @tensorPullbackIsoReindex_hom_base X.functionField X'.functionField
    Y.obj.left.functionField inferInstance inferInstance inferInstance
    (baseChangeFieldAlgebra j g) (GenericGalois.algebra Y) X U Y.obj.left Y.obj.hom g
    (X.fromSpecStalk (genericPoint X))
    (originalGenericFibreIso Y) (originalGenericFibreIso_hom_snd Y)
    U.functionField inferInstance (U.fromSpecStalk (genericPoint U)) (openGenericIso j)
    (openGenericMap_generic j g) X' j (X'.fromSpecStalk (genericPoint X'))
    (openGenericMap_over j)

/-- The comparison is over the unchanged ambient function-field spectrum. -/
@[reassoc] theorem baseChangeFieldSpectrumIso_hom_over :
    letI := baseChangeFieldAlgebra j g
    (baseChangeFieldSpectrumIso j g Y).hom ≫
        (genericCover j ((baseChange g).obj Y).obj.hom).obj.hom =
      Spec.algebraMap X'.functionField
        (X'.functionField ⊗[X.functionField] Y.obj.left.functionField) := by
  let := baseChangeFieldAlgebra j g
  apply (cancel_mono (X'.fromSpecStalk (genericPoint X'))).mp
  simpa only [Category.assoc, genericMap] using
    baseChangeFieldSpectrumIso_hom_genericMap j g Y

/-- The comparison retains the projection to the original covering scheme,
through its unchanged function-field spectrum and the right tensor inclusion. -/
@[reassoc] theorem baseChangeFieldSpectrumIso_hom_genericToCover :
    letI := baseChangeFieldAlgebra j g
    (baseChangeFieldSpectrumIso j g Y).hom ≫
        genericToCover j ((baseChange g).obj Y).obj.hom ≫ pullback.fst Y.obj.hom g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Y.obj.left.functionField →ₐ[X.functionField]
          X'.functionField ⊗[X.functionField] Y.obj.left.functionField).toRingHom) ≫
            Y.obj.left.fromSpecStalk (genericPoint Y.obj.left) := by
  let := baseChangeFieldAlgebra j g
  exact @tensorPullbackIsoReindex_hom_source X.functionField X'.functionField
    Y.obj.left.functionField inferInstance inferInstance inferInstance
    (baseChangeFieldAlgebra j g) (GenericGalois.algebra Y) X U Y.obj.left Y.obj.hom g
    (X.fromSpecStalk (genericPoint X))
    (originalGenericFibreIso Y) (originalGenericFibreIso_hom_snd Y)
    U.functionField inferInstance (U.fromSpecStalk (genericPoint U)) (openGenericIso j)
    (openGenericMap_generic j g) (Y.obj.left.fromSpecStalk (genericPoint Y.obj.left))
    (originalGenericFibreIso_hom_fst Y)

section AffineScalars

set_option backward.isDefEq.respectTransparency false in
local instance affineFunctionFieldAlgebra (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)

variable (R A T B : Type u) [CommRing R]
  [CommRing A] [IsDomain A] [CommRing T] [IsDomain T] [CommRing B] [IsDomain B]
  [Algebra R A] [Algebra R T] [Algebra R B] [Algebra A B] [Algebra T B]
  [IsScalarTower R A B] [IsScalarTower R T B]
  [Algebra R (Spec (.of A)).functionField] [Algebra R (Spec (.of T)).functionField]
  [IsScalarTower R A (Spec (.of A)).functionField]
  [IsScalarTower R T (Spec (.of T)).functionField]
  [IsOpenImmersion (Spec.algebraMap T B)] [IsDominant (Spec.algebraMap A B)]

set_option backward.isDefEq.respectTransparency false in
/-- The original affine coefficient square supplies the scalar tower on the
same function fields used by the generic tensor comparison. -/
theorem baseChangeFieldAlgebra_isScalarTower :
    letI := baseChangeFieldAlgebra (Spec.algebraMap T B) (Spec.algebraMap A B)
    IsScalarTower R (Spec (.of A)).functionField (Spec (.of T)).functionField := by
  let := baseChangeFieldAlgebra (Spec.algebraMap T B) (Spec.algebraMap A B)
  let : IsDominant (Spec.algebraMap T B) :=
    Scheme.isDominant_of_isOpenImmersion (Spec.algebraMap T B)
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R (Spec (.of T)).functionField r =
    baseChangeFieldHom (Spec.algebraMap T B) (Spec.algebraMap A B)
      (algebraMap R (Spec (.of A)).functionField r)
  apply (FunctionField.fieldEquiv (Spec.algebraMap T B)).injective
  rw [baseChangeFieldHom_open]
  change functionFieldMap (Spec.algebraMap T B)
      (algebraMap R (Spec (.of T)).functionField r) =
    functionFieldMap (Spec.algebraMap A B)
      (algebraMap R (Spec (.of A)).functionField r)
  rw [IsScalarTower.algebraMap_apply R T (Spec (.of T)).functionField,
    IsScalarTower.algebraMap_apply R A (Spec (.of A)).functionField]
  have hT := RingHom.congr_fun
    (FunctionField.AffineCompatibility.fieldMap_spec_constants (.of B) (.of T)
      (CommRingCat.ofHom (algebraMap T B))) (algebraMap R T r)
  have hA := RingHom.congr_fun
    (FunctionField.AffineCompatibility.fieldMap_spec_constants (.of B) (.of A)
      (CommRingCat.ofHom (algebraMap A B))) (algebraMap R A r)
  change functionFieldMap (Spec.algebraMap T B)
    (algebraMap T (Spec (.of T)).functionField (algebraMap R T r)) = _ at hT
  change functionFieldMap (Spec.algebraMap A B)
    (algebraMap A (Spec (.of A)).functionField (algebraMap R A r)) = _ at hA
  rw [hT, hA]
  change algebraMap B (Spec (.of B)).functionField
      (algebraMap T B (algebraMap R T r)) =
    algebraMap B (Spec (.of B)).functionField (algebraMap A B (algebraMap R A r))
  rw [← IsScalarTower.algebraMap_apply R T B, ← IsScalarTower.algebraMap_apply R A B]

end AffineScalars

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (Y : Scheme.FiniteEtale U) [IsIntegral Y.obj.left]

local instance originalCoverDominant : IsDominant Y.obj.hom := GenericGalois.dominant Y

/-- The original covering field spectrum is the unchanged generic source,
with only the native pullback symmetry changing its displayed orientation. -/
def originalFieldSpectrumIso :
    Spec Y.obj.left.functionField ≅ (genericCover j Y.obj.hom).obj.left :=
  originalGenericFibreIso Y ≪≫
    pullbackSymmetry Y.obj.hom (U.fromSpecStalk (genericPoint U))

/-- The original covering-source triangle of the generic field comparison. -/
@[reassoc] theorem originalFieldSpectrumIso_hom_toCover :
    (originalFieldSpectrumIso j Y).hom ≫ genericToCover j Y.obj.hom =
      Y.obj.left.fromSpecStalk (genericPoint Y.obj.left) := by
  change ((originalGenericFibreIso Y).hom ≫
    (pullbackSymmetry Y.obj.hom (U.fromSpecStalk (genericPoint U))).hom) ≫
      pullback.snd _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
    originalGenericFibreIso_hom_fst]

/-- The original ambient-base triangle of the same generic field comparison. -/
@[reassoc] theorem originalFieldSpectrumIso_hom_genericMap :
    (originalFieldSpectrumIso j Y).hom ≫ genericMap j Y.obj.hom =
      Y.obj.left.fromSpecStalk (genericPoint Y.obj.left) ≫ Y.obj.hom ≫ j := by
  rw [genericMap_eq]
  simp only [Category.assoc, originalFieldSpectrumIso_hom_toCover_assoc]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
