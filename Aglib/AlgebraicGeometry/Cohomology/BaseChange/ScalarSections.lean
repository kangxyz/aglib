/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Nonzero
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NativeScalarSections
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Original scalar sections after flat base change

The degree-zero comparison and the native pullback-unit isomorphism preserve
bijectivity of the actual structural map into global functions. The proof
retains the original scalar homomorphisms and the original cartesian square;
no alternate global-section or cohomology model is selected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  {X Y : Scheme.{u}} (p : Y ⟶ X) (σ : A →+* B)
  (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)

/-- Invertibility of the actual degree-zero tensor comparison reflects the
original scalar-section isomorphism across the original square. -/
theorem scalarSections_bijective_of_baseChange_isIso
    (hα : Function.Bijective α)
    [IsIso (moduleCohomologyTensorMap p σ α β h
      ((Modules.pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit X.ringCatSheaf)) 0)] :
    Function.Bijective β := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : Y.Modules := (Modules.pullback p).obj M
  let : Algebra A B := σ.toAlgebra
  let : Module A Γ(M, ⊤) := Module.compHom _ α
  let : Module B Γ(N, ⊤) := Module.compHom _ β
  let : Module B Γ(Y, ⊤) := Module.compHom _ β
  let := moduleCohomologyModuleOfHom X α M 0
  let := moduleCohomologyModuleOfHom Y β N 0
  let a : A →ₗ[A] Γ(M, ⊤) :=
    { __ := α.toAddMonoidHom
      map_smul' := fun r s => α.map_mul r s }
  let eA : A ≃ₗ[A] Γ(M, ⊤) := LinearEquiv.ofBijective a hα
  let eX : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0 ≃ₗ[A] Γ(M, ⊤) :=
    moduleH0EquivOfHom X α M
  let eY : Sheaf.H.{u + 1} (moduleAddSheaf Y N) 0 ≃ₗ[B] Γ(N, ⊤) :=
    moduleH0EquivOfHom Y β N
  let C : (ModuleCat.extendScalars σ).obj
      (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0)) ⟶
      ModuleCat.of B (Sheaf.H.{u + 1} (moduleAddSheaf Y N) 0) :=
    moduleCohomologyTensorMap p σ α β h
    ((Modules.pullbackPushforwardAdjunction p).unit.app M) 0
  let eC := (asIso C).toLinearEquiv
  let eU : Γ(N, ⊤) ≃ₗ[B] Γ(Y, ⊤) :=
    (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)) ⋙
    ModuleCat.restrictScalars β).mapIso (Modules.pullbackUnitIso p)).toLinearEquiv
  let e : B ≃ₗ[B] Γ(Y, ⊤) :=
    (TensorProduct.AlgebraTensorModule.rid A B B).symm.trans
      (((eA.trans eX.symm).baseChange A B _ _).trans
        (eC.trans (eY.trans eU)))
  have he : e (1 : B) = 1 := by
    change eU (eY (C ((1 : B) ⊗ₜ[A] (eX.symm (α 1))))) = 1
    rw [map_one]
    have hC := moduleCohomologyTensorMap_one_tmul p σ α β h
      ((Modules.pullbackPushforwardAdjunction p).unit.app M) 0 (eX.symm (1 : Γ(X, ⊤)))
    change C ((1 : B) ⊗ₜ[A] (eX.symm (1 : Γ(X, ⊤)))) =
      moduleCohomologyPullback p M 0 (eX.symm (1 : Γ(X, ⊤))) at hC
    rw [hC]
    change (Modules.pullbackUnitIso p).hom.app ⊤
      (Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop
        (moduleCohomologyPullback p M 0 (eX.symm (1 : Γ(X, ⊤))))) = (1 : Γ(Y, ⊤))
    rw [moduleCohomologyPullback_equiv₀]
    change (Modules.pullbackUnitIso p).hom.app ⊤
      (((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
        (eX (eX.symm (1 : Γ(X, ⊤))))) = (1 : Γ(Y, ⊤))
    rw [LinearEquiv.apply_symm_apply]
    exact pullbackUnitIso_unit_one p
  have heq (b : B) : e b = β b := by
    calc
      e b = e (b • (1 : B)) := by rw [smul_eq_mul, mul_one]
      _ = b • e 1 := e.map_smul b 1
      _ = β b := by rw [he]; change β b * 1 = β b; exact mul_one _
  have heq' : (fun b => e b) = β := funext heq
  rw [← heq']
  exact e.bijective

end AlgebraicGeometry.Scheme.Cohomology
