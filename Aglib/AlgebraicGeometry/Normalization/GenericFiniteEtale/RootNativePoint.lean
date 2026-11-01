/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.AffineMap
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointLift
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootEmbedding

/-! # The specified point of the original native normalization

The literal tensor integral-closure map is transported through the original
source comparisons to a map of the native normalizations. Its base and generic
triangles are retained. The original point lifts along this map to the closed
root base. This is a map, not a ramified normalization base-change isomorphism;
the original normalization is not identified with the original open cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.Kummer
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Lift the specified point of the original native normalization to the
native normalized root cover through the constructed original closure map.
Both original structural triangles and the exact point image are retained. -/
theorem exists_nativeNormalizedRootPoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})]
    (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f) :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    let U := Localization.Away f
    let T := RootAlgebra N f
    let V := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left],
    let K := (Spec (.of U)).functionField
    let F := (Spec (.of T)).functionField
    let L := Y.obj.left.functionField
    let g := Spec.map (CommRingCat.ofHom (rootComplementHom N f))
    let j := Spec.algebraMap T V
    letI : IsDominant g := rootComplement_dominant R N f hN (parameter_ne_zero R f hreg)
    letI : Algebra K F := OpenRecovery.baseChangeFieldAlgebra j g
    letI : Algebra K L := GenericGalois.algebra Y
    let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
    let q₁ := OpenRecovery.genericMap j ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
    let e₀ := OpenRecovery.originalFieldSpectrumIso (Spec.algebraMap R U) Y
    let e₁ := OpenRecovery.baseChangeFieldSpectrumIso j g Y
    ∀ x : q₀.normalization, q₀.fromNormalization x = IsLocalRing.closedPoint R →
    ∃ m : q₁.normalization ⟶ q₀.normalization,
      m ≫ q₀.fromNormalization = q₁.fromNormalization ≫ Spec.algebraMap R T ∧
      e₁.hom ≫ q₁.toNormalization ≫ m =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toRingHom) ≫
          e₀.hom ≫ q₀.toNormalization ∧
      ∃ y : q₁.normalization, m y = x ∧
        q₁.fromNormalization y = IsLocalRing.closedPoint T := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let T := RootAlgebra N f
  let V := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  dsimp only
  intro Y hY
  let K := (Spec (.of U)).functionField
  let F := (Spec (.of T)).functionField
  let L := Y.obj.left.functionField
  let : Algebra U V := (rootComplementHom N f).toAlgebra
  let : IsScalarTower R U V :=
    IsScalarTower.of_algebraMap_eq fun r => (rootComplementHom_algebraMap N f r).symm
  let g := Spec.map (CommRingCat.ofHom (rootComplementHom N f))
  let j := Spec.algebraMap T V
  let : IsDominant g := rootComplement_dominant R N f hN (parameter_ne_zero R f hreg)
  let : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
  let : Algebra T F := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of T)
  let : IsFractionRing T F := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of T)
  let : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
  let : IsScalarTower R U K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R F := ((algebraMap T F).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra K F := OpenRecovery.baseChangeFieldAlgebra j g
  let : IsScalarTower R K F := OpenRecovery.baseChangeFieldAlgebra_isScalarTower R U T V
  let : Algebra K L := GenericGalois.algebra Y
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale K L := (GenericGalois.functionField_finiteEtale Y).2
  let A := F ⊗[K] L
  let i : L →ₐ[R] A := (Algebra.TensorProduct.includeRight : L →ₐ[K] A).restrictScalars R
  let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
  let q₁ := OpenRecovery.genericMap j ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
  let e₀ := OpenRecovery.originalFieldSpectrumIso (Spec.algebraMap R U) Y
  let e₁ := OpenRecovery.baseChangeFieldSpectrumIso j g Y
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  have he₀ : e₀.hom ≫ q₀ = Spec.algebraMap R L := by
    rw [OpenRecovery.originalFieldSpectrumIso_hom_genericMap,
      ← Category.assoc, fromSpecStalk_genericPoint_naturality Y.obj.hom, Spec.fromSpecStalk_eq']
    change (Spec.algebraMap K L ≫ Spec.algebraMap U K) ≫ Spec.algebraMap R U = _
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have he₁ : e₁.hom ≫ q₁ = Spec.algebraMap T A := by
    rw [OpenRecovery.baseChangeFieldSpectrumIso_hom_genericMap, Spec.fromSpecStalk_eq']
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  let n₀ := Hom.integralClosureSourceIso R L q₀ e₀ he₀
  let n₁ := Hom.integralClosureSourceIso T A q₁ e₁ he₁
  let m := Hom.integralClosureNormalizationMap R T L A i q₀ q₁ e₀ e₁ he₀ he₁
  intro x hx
  refine ⟨m, Hom.integralClosureNormalizationMap_over R T L A i q₀ q₁ e₀ e₁ he₀ he₁,
    Hom.integralClosureNormalizationMap_generic R T L A i q₀ q₁ e₀ e₁ he₀ he₁, ?_⟩
  have hx₀ : Spec.algebraMap R (integralClosure R L) (n₀.inv x) =
      IsLocalRing.closedPoint R := by
    have h := congrArg (fun a => a (n₀.inv x))
      (Hom.integralClosureSourceIso_hom_over R L q₀ e₀ he₀)
    change q₀.fromNormalization (n₀.hom (n₀.inv x)) = _ at h
    rw [Scheme.inv_hom_apply] at h
    exact h.symm.trans hx
  obtain ⟨y, hy, hyT⟩ := exists_normalizedRootPoint R f hf N hN hreg K F L (n₀.inv x) hx₀
  refine ⟨n₁.hom y, ?_, ?_⟩
  · have h := congrArg (fun a => a y)
      (Hom.integralClosureNormalizationMap_chart R T L A i q₀ q₁ e₀ e₁ he₀ he₁)
    change m (n₁.hom y) = n₀.hom
      (Spec.map (CommRingCat.ofHom (integralClosure.tensorChangeBaseMap R T K F L).toRingHom) y)
      at h
    rw [hy] at h
    exact h.trans (Scheme.inv_hom_apply n₀ x)
  · have h := congrArg (fun a => a y)
      (Hom.integralClosureSourceIso_hom_over T A q₁ e₁ he₁)
    exact h.trans hyT

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
