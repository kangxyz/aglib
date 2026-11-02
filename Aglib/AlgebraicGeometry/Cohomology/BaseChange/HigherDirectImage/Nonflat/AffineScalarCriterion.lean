/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ScalarMate
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Isomorphisms

/-! # Original affine sheaf maps and their scalar-adjunction mates

For actual quasicoherent affine sheaves, a unit-pure-tensor law identifies
Gamma of the original sheaf map with the original small scalar mate. The
large scalar mate is invertible exactly when the original sheaf map is.
No cohomology, derived realization or geometric comparison is assumed here.
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
  (k : P ⟶ (ModuleCat.restrictScalars σ.hom).obj Q)
  (hunit : ∀ x : moduleSpecΓFunctor.obj E,
    d (moduleSpecΓFunctor.map φ
      ((affinePullbackGlobalSectionsIso σ E).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) = k (e x))

include hunit

/-- The unit-pure-tensor law determines the entire original scalar-extended section map. -/
theorem affineScalarCriterion_sections :
    (affinePullbackGlobalSectionsIso σ E).hom ≫ moduleSpecΓFunctor.map φ =
      smallTensorMap σ.hom e d k := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply d.injective
  exact (hunit x).trans (smallTensorMap_one_tmul σ.hom e d k x).symm

/-- Original affine sheaf-map invertibility is equivalent to original scalar-mate
invertibility, using only the proved unit law and actual quasicoherence. -/
theorem affineScalarCriterion_isIso_iff [F.IsQuasicoherent] :
    IsIso φ ↔
      IsIso (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ.hom).homEquiv _ _).symm k) := by
  rw [← smallTensorMap_isIso_iff σ.hom e d k]
  have hsections := affineScalarCriterion_sections σ E F φ e d k hunit
  constructor
  · intro h
    let := h
    rw [← hsections]
    infer_instance
  · intro h
    let := h
    have : IsIso ((affinePullbackGlobalSectionsIso σ E).hom ≫
        moduleSpecΓFunctor.map φ) := by rw [hsections]; infer_instance
    have : IsIso (moduleSpecΓFunctor.map φ) :=
      IsIso.of_isIso_comp_left (affinePullbackGlobalSectionsIso σ E).hom _
    let : ((pullback (Spec.map σ)).obj E).IsQuasicoherent :=
      isQuasicoherent_pullback σ E
    exact QuasiCoherent.affine_isIso_of_globalSections S φ

end AlgebraicGeometry.Scheme.Modules.Nonflat
