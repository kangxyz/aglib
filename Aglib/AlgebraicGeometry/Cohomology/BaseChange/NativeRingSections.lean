/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NativeScalarSections
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The original ring of sections under flat affine base change

The actual algebra map sends b tensor a to the product of the two original
section maps. Native module flat base change proves bijectivity of this same
map; no arbitrary linear equivalence is promoted to a ring equivalence.
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

/-- The original ring tensor comparison, with the unchanged scalar maps. -/
def ringSectionsTensorAlgHom :
    letI := σ.toAlgebra
    letI := α.toAlgebra
    letI := β.toAlgebra
    B ⊗[A] Γ(X, ⊤) →ₐ[B] Γ(Y, ⊤) := by
  letI := σ.toAlgebra
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI : Algebra A Γ(Y, ⊤) := (β.comp σ).toAlgebra
  letI : IsScalarTower A B Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : Γ(X, ⊤) →ₐ[A] Γ(Y, ⊤) :=
    { __ := p.appTop.hom
      commutes' := fun a => RingHom.congr_fun h a }
  exact AlgHom.liftEquiv A B Γ(X, ⊤) Γ(Y, ⊤) g

/-- The defining formula records both actual legs of the original square. -/
@[simp]
theorem ringSectionsTensorAlgHom_tmul (b : B) (a : Γ(X, ⊤)) :
    letI := σ.toAlgebra
    letI := α.toAlgebra
    letI := β.toAlgebra
    ringSectionsTensorAlgHom p σ α β h (b ⊗ₜ[A] a) = β b * p.appTop a := rfl

/-- Native module comparison proves bijectivity of the exact ring map. -/
theorem ringSectionsTensorAlgHom_bijective_of_sections_isIso
    [IsIso ((moduleSectionsTensorComparison p α β σ h
      (SheafOfModules.unit X.ringCatSheaf)).app (op ⊤))] :
    Function.Bijective (ringSectionsTensorAlgHom p σ α β h) := by
  let := σ.toAlgebra
  let := α.toAlgebra
  let := β.toAlgebra
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : Y.Modules := (Modules.pullback p).obj M
  let : Module A Γ(M, ⊤) := Module.compHom _ α
  let : Module B Γ(N, ⊤) := Module.compHom _ β
  let eX := (moduleTopSectionsIso X α M).toLinearEquiv
  let eY := (moduleTopSectionsIso Y β N).toLinearEquiv
  let C := (moduleSectionsTensorComparison p α β σ h M).app (op ⊤)
  let eC := (asIso C).toLinearEquiv
  let eU : Γ(N, ⊤) ≃ₗ[B] Γ(Y, ⊤) :=
    (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)) ⋙
      ModuleCat.restrictScalars β).mapIso (Modules.pullbackUnitIso p)).toLinearEquiv
  let e : B ⊗[A] Γ(X, ⊤) ≃ₗ[B] Γ(Y, ⊤) :=
    (eX.symm.baseChange A B _ _).trans (eC.trans (eY.trans eU))
  have he (a : Γ(X, ⊤)) : e (1 ⊗ₜ[A] a) = p.appTop a := by
    change eU (eY (C ((1 : B) ⊗ₜ[A] (eX.symm a)))) = _
    have hC := moduleSectionsTensorComparison_one_tmul p α β σ h M ⊤ (eX.symm a)
    change C ((1 : B) ⊗ₜ[A] (eX.symm a)) =
      ((Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ a at hC
    rw [hC]
    have hu := Modules.pullbackUnitIso_homEquiv p
    change (Modules.pullbackPushforwardAdjunction p).unit.app M ≫
      (Modules.pushforward p).map (Modules.pullbackUnitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom at hu
    exact congrArg (fun k : M ⟶ (Modules.pushforward p).obj
      (SheafOfModules.unit Y.ringCatSheaf) => Modules.Hom.app k ⊤ a) hu
  have heq (z : B ⊗[A] Γ(X, ⊤)) :
      e z = ringSectionsTensorAlgHom p σ α β h z := by
    induction z using TensorProduct.inductionOn with
    | tmul b a =>
      calc
        e (b ⊗ₜ[A] a) = b • e (1 ⊗ₜ[A] a) := by
          rw [← e.map_smul]
          apply congrArg e
          change b ⊗ₜ[A] a = (b * 1) ⊗ₜ[A] a
          rw [mul_one]
        _ = β b * p.appTop a := by rw [he]; rfl
        _ = ringSectionsTensorAlgHom p σ α β h (b ⊗ₜ[A] a) := rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [← show (fun z => e z) = ringSectionsTensorAlgHom p σ α β h from funext heq]
  exact e.bijective

/-- The actual algebra comparison is bijective on the unchanged qcqs flat
base-change square. -/
theorem ringSectionsTensorAlgHom_bijective_of_flat_of_isPullback
    (q : Y ⟶ Spec (.of B)) (f : X ⟶ Spec (.of A))
    [QuasiCompact f] [QuasiSeparated f]
    (H : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat) :
    Function.Bijective (ringSectionsTensorAlgHom p σ
      (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom)
      (q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom)
      (moduleSectionsBaseChangeScalars p q f σ H.w)) := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : M.IsQuasicoherent := Modules.isQuasicoherent_unit X
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := moduleSectionsTensorComparison_isIso_app_of_flat_of_isPullback
    p q f σ H hflat M ⊤ isCompact_univ
  exact ringSectionsTensorAlgHom_bijective_of_sections_isIso p σ _ _ _

/-- The algebra equivalence has the literal tensor comparison as its forward
map; its inverse is obtained only after proving that same map bijective. -/
def ringSectionsTensorAlgEquivOfFlatOfIsPullback
    (q : Y ⟶ Spec (.of B)) (f : X ⟶ Spec (.of A))
    [QuasiCompact f] [QuasiSeparated f]
    (H : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) (hflat : σ.Flat) :
    letI := σ.toAlgebra
    letI := (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom).toAlgebra
    letI := (q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom).toAlgebra
    B ⊗[A] Γ(X, ⊤) ≃ₐ[B] Γ(Y, ⊤) :=
  by
    letI := σ.toAlgebra
    letI := (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom).toAlgebra
    letI := (q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom).toAlgebra
    exact AlgEquiv.ofBijective (ringSectionsTensorAlgHom p σ _ _
      (moduleSectionsBaseChangeScalars p q f σ H.w))
      (ringSectionsTensorAlgHom_bijective_of_flat_of_isPullback p σ q f H hflat)

end AlgebraicGeometry.Scheme.Cohomology
