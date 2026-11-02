/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineScalarCriterion

/-! # Affine comparison with an original scalar-extension map

The public data contain the original tensor map, not an additional restricted
scalar action. The generic proof uses the existing adjunction and scalar criterion.
-/

@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {R S : CommRingCat.{u}} (σ : R ⟶ S)
  (E : (Spec R).Modules) (F : (Spec S).Modules) [E.IsQuasicoherent]
  (φ : (pullback (Spec.map σ)).obj E ⟶ F)
  {P : ModuleCat.{u + 1} R} {Q : ModuleCat.{u + 1} S}
  (e : moduleSpecΓFunctor.obj E ≃ₗ[R] P) (d : moduleSpecΓFunctor.obj F ≃ₗ[S] Q)
  (δ : (ModuleCat.extendScalars σ.hom).obj P ⟶ Q)
  (hunit : ∀ x : moduleSpecΓFunctor.obj E,
    d (moduleSpecΓFunctor.map φ
      ((affinePullbackGlobalSectionsIso σ E).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
      δ ((1 : S) ⊗ₜ[R,σ.hom] e x))

include hunit

/-- The original unit law determines the whole Gamma square with the original tensor map. -/
theorem affineTensorCriterion_sections :
    let := σ.hom.toAlgebra
    ((affinePullbackGlobalSectionsIso σ E).hom ≫ moduleSpecΓFunctor.map φ).hom =
      d.symm.toLinearMap.comp (δ.hom.comp (e.baseChange R S _ _).toLinearMap) := by
  let := σ.hom.toAlgebra
  let k := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ.hom).homEquiv _ _ δ
  have hk : ∀ x : moduleSpecΓFunctor.obj E,
      d (moduleSpecΓFunctor.map φ
        ((affinePullbackGlobalSectionsIso σ E).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
        k (e x) := by
    intro x
    exact hunit x
  rw [affineScalarCriterion_sections σ E F φ e d k hk]
  simpa only [k, Equiv.symm_apply_apply] using smallTensorMap_conjugate σ.hom e d k

/-- Original affine-map invertibility is precisely original tensor-map invertibility. -/
theorem affineTensorCriterion_isIso_iff [F.IsQuasicoherent] :
    IsIso φ ↔ IsIso δ := by
  let k := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ.hom).homEquiv _ _ δ
  have hk : ∀ x : moduleSpecΓFunctor.obj E,
      d (moduleSpecΓFunctor.map φ
        ((affinePullbackGlobalSectionsIso σ E).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
        k (e x) := by
    intro x
    exact hunit x
  simpa only [k, Equiv.symm_apply_apply] using
    affineScalarCriterion_isIso_iff σ E F φ e d k hk

end AlgebraicGeometry.Scheme.Modules.Nonflat
