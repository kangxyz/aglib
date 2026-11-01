/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Flat
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitOne
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
theorem scalarSections_bijective_of_sections_isIso
    (hα : Function.Bijective α)
    [IsIso ((moduleSectionsTensorComparison p α β σ h
      (SheafOfModules.unit X.ringCatSheaf)).app (op ⊤))] :
    Function.Bijective β := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : Y.Modules := (Modules.pullback p).obj M
  let : Algebra A B := σ.toAlgebra
  let : Module A Γ(M, ⊤) := Module.compHom _ α
  let : Module B Γ(N, ⊤) := Module.compHom _ β
  let : Module B Γ(Y, ⊤) := Module.compHom _ β
  let a : A →ₗ[A] Γ(M, ⊤) :=
    { __ := α.toAddMonoidHom
      map_smul' := fun r s => α.map_mul r s }
  let eA : A ≃ₗ[A] Γ(M, ⊤) := LinearEquiv.ofBijective a hα
  let eX := (moduleTopSectionsIso X α M).toLinearEquiv
  let eY := (moduleTopSectionsIso Y β N).toLinearEquiv
  let C := (moduleSectionsTensorComparison p α β σ h M).app (op ⊤)
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
    have hC := moduleSectionsTensorComparison_one_tmul p α β σ h M ⊤
      (eX.symm (1 : Γ(X, ⊤)))
    change C ((1 : B) ⊗ₜ[A] (eX.symm (1 : Γ(X, ⊤)))) =
      ((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
        (1 : Γ(X, ⊤)) at hC
    rw [hC]
    change (Modules.pullbackUnitIso p).hom.app ⊤
      (((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤
        (1 : Γ(X, ⊤))) = (1 : Γ(Y, ⊤))
    exact pullbackUnitIso_unit_one p
  have heq (b : B) : e b = β b := by
    calc
      e b = e (b • (1 : B)) := by rw [smul_eq_mul, mul_one]
      _ = b • e 1 := e.map_smul b 1
      _ = β b := by rw [he]; change β b * 1 = β b; exact mul_one _
  have heq' : (fun b => e b) = β := funext heq
  rw [← heq']
  exact e.bijective

/-- Flat base change preserves original scalar-section bijectivity for qcqs
morphisms, on the actual supplied cartesian square. -/
theorem scalarSections_bijective_of_flat_of_isPullback
    (q : Y ⟶ Spec (.of B)) (f : X ⟶ Spec (.of A))
    [QuasiCompact f] [QuasiSeparated f]
    (H : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat)
    (hf : Function.Bijective (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom)) :
    Function.Bijective (q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom) := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let α := f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom
  let β := q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom
  let h := moduleSectionsBaseChangeScalars p q f σ H.w
  let : M.IsQuasicoherent := Modules.isQuasicoherent_unit X
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := moduleSectionsTensorComparison_isIso_app_of_flat_of_isPullback
    p q f σ H hflat M ⊤ isCompact_univ
  exact scalarSections_bijective_of_sections_isIso p σ α β h hf

end AlgebraicGeometry.Scheme.Cohomology
