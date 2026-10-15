/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open

/-!
# Original open and coefficient naturality of resolution-section cohomology

The actual restriction and coefficient-resolution maps on sections induce
the unchanged native open-cohomology maps under the original comparison.
Both statements preserve the original Ext classes and native cycle values.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R]

variable (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

section Coefficients

variable (U : X.Opens) {M N : X.Modules} (I : InjectiveResolution M)
  (J : InjectiveResolution N) {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f)

/-- The original resolution lift on actual section cycles over the indicated open. -/
def moduleResolutionOpenSectionCyclesMap (n : ℕ) :
    moduleResolutionOpenSectionCycles X α U I n →ₗ[R]
      moduleResolutionOpenSectionCycles X α U J n := by
  let a := ((moduleOpenSectionsFunctorOfHom X α U).mapHomologicalComplex (.up ℤ)).map φ.hom'
  refine {
    toFun := fun s ↦ ⟨a.f n s.val, ?_⟩
    map_add' := fun s t ↦ Subtype.ext ((a.f n).hom.map_add _ _)
    map_smul' := fun r s ↦ Subtype.ext ((a.f n).hom.map_smul _ _) }
  have h := congrArg
    (fun g : (moduleResolutionOpenSectionComplex X α U I).X n ⟶
        (moduleResolutionOpenSectionComplex X α U J).X ((n : ℤ) + 1) ↦ g s.val)
    (a.comm n ((n : ℤ) + 1))
  change _ = a.f ((n : ℤ) + 1)
    (((moduleResolutionOpenSectionComplex X α U I).d n ((n : ℤ) + 1)) s.val) at h
  rw [s.property, map_zero] at h
  exact h

theorem moduleResolutionOpenSectionCyclesMap_apply (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    (moduleResolutionOpenSectionCyclesMap X α U I J φ n s).val =
      Scheme.Modules.Hom.app (φ.hom'.f n) U s.val := rfl

/-- Original represented section morphisms preserve the supplied coefficient-resolution lift. -/
theorem moduleResolutionOpenSectionHom_naturality (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionHom X α U J n
        (moduleResolutionOpenSectionCyclesMap X α U I J φ n s) =
      moduleResolutionOpenSectionHom X α U I n s ≫ φ.hom.f n := by
  have h :
      (Scheme.Modules.openFreeHomAddEquiv X U (J.cochainComplex.X n)).symm
          (Scheme.Modules.Hom.app (φ.hom'.f n) U s.val) =
        (Scheme.Modules.openFreeHomAddEquiv X U (I.cochainComplex.X n)).symm s.val ≫
          φ.hom'.f n := by
    apply (Scheme.Modules.openFreeHomAddEquiv X U _).injective
    rw [AddEquiv.apply_symm_apply]
    change _ = Scheme.Modules.openFreeHomEquiv X U _ (_ ≫ _)
    rw [Scheme.Modules.openFreeHomEquiv_comp]
    change Scheme.Modules.Hom.app (φ.hom'.f n) U s.val =
      Scheme.Modules.Hom.app (φ.hom'.f n) U
        ((Scheme.Modules.openFreeHomAddEquiv X U _)
          ((Scheme.Modules.openFreeHomAddEquiv X U _).symm s.val))
    rw [AddEquiv.apply_symm_apply]
  dsimp only [moduleResolutionOpenSectionHom]
  change (Scheme.Modules.openFreeHomAddEquiv X U _).symm
    (Scheme.Modules.Hom.app (φ.hom'.f n) U s.val) ≫ _ = _
  rw [h, φ.hom'_f n n rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original coefficient action on native `H'` agrees with the actual lifted cycle map. -/
theorem moduleResolutionOpenSectionClass_naturality (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleHPrimeMapOfHom X α f n U (moduleResolutionOpenSectionClass X α U I n s) =
      moduleResolutionOpenSectionClass X α U J n
        (moduleResolutionOpenSectionCyclesMap X α U I J φ n s) := by
  change (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f)).app (op U))
        (moduleOpenExtCohomologyMap X U M n (moduleResolutionOpenSectionExtClass X α U I n s)) =
    moduleOpenExtCohomologyMap X U N n
      (moduleResolutionOpenSectionExtClass X α U J n
        (moduleResolutionOpenSectionCyclesMap X α U I J φ n s))
  rw [← moduleOpenExtCohomologyMap_naturality X U f n]
  apply congrArg (moduleOpenExtCohomologyMap X U N n)
  rw [moduleResolutionOpenSectionExtClass_eq_extMk,
    moduleResolutionOpenSectionExtClass_eq_extMk, InjectiveResolution.extMk_comp_mk₀ _ _ _ _ φ]
  congr 1
  exact (moduleResolutionOpenSectionHom_naturality X α U I J φ n s).symm

/-- Actual section homology of every supplied native resolution lift is the unchanged
coefficient map on original open cohomology. -/
theorem moduleResolutionOpenSectionsCohomologyLinearEquiv_naturality (n : ℕ)
    (x : (moduleResolutionOpenSectionComplex X α U I).homology (n : ℤ)) :
    let a := ((moduleOpenSectionsFunctorOfHom X α U).mapHomologicalComplex (.up ℤ)).map φ.hom'
    moduleResolutionOpenSectionsCohomologyLinearEquiv X α U J n
        (HomologicalComplex.homologyMap a (n : ℤ) x) =
      moduleHPrimeMapOfHom X α f n U
        (moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n x) := by
  let K := moduleResolutionOpenSectionComplex X α U I
  let L := moduleResolutionOpenSectionComplex X α U J
  let a := ((moduleOpenSectionsFunctorOfHom X α U).mapHomologicalComplex (.up ℤ)).map φ.hom'
  change moduleResolutionOpenSectionsCohomologyLinearEquiv X α U J n
      (HomologicalComplex.homologyMap a (n : ℤ) x) =
    moduleHPrimeMapOfHom X α f n U
      (moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n x)
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance) x
  have hπ := congrArg (fun k ↦ k c) (HomologicalComplex.homologyπ_naturality a (n : ℤ))
  change HomologicalComplex.homologyMap a (n : ℤ) (K.homologyπ n c) =
    L.homologyπ n (HomologicalComplex.cyclesMap a (n : ℤ) c) at hπ
  rw [hπ, moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ X α U J n,
    moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ X α U I n,
    moduleResolutionOpenSectionClass_naturality X α U I J φ n]
  apply congrArg (moduleResolutionOpenSectionClass X α U J n)
  apply Subtype.ext
  rw [moduleResolutionOpenSectionCyclesIso_hom_val, moduleResolutionOpenSectionCyclesMap_apply,
    moduleResolutionOpenSectionCyclesIso_hom_val]
  exact congrArg (fun k ↦ k c) (HomologicalComplex.cyclesMap_i a (n : ℤ))

end Coefficients

section Restriction

variable {U V : X.Opens} (i : U ⟶ V) {M : X.Modules} (I : InjectiveResolution M)

/-- The unchanged open restriction on actual resolution-section cycles. -/
def moduleResolutionOpenSectionCyclesRestriction (n : ℕ) :
    moduleResolutionOpenSectionCycles X α V I n →ₗ[R]
      moduleResolutionOpenSectionCycles X α U I n := by
  let a := moduleResolutionOpenSectionRestriction X α i I
  refine {
    toFun := fun s ↦ ⟨a.f n s.val, ?_⟩
    map_add' := fun s t ↦ Subtype.ext ((a.f n).hom.map_add _ _)
    map_smul' := fun r s ↦ Subtype.ext ((a.f n).hom.map_smul _ _) }
  have h := congrArg
    (fun g : (moduleResolutionOpenSectionComplex X α V I).X n ⟶
        (moduleResolutionOpenSectionComplex X α U I).X ((n : ℤ) + 1) ↦ g s.val)
    (a.comm n ((n : ℤ) + 1))
  change _ = a.f ((n : ℤ) + 1)
    (((moduleResolutionOpenSectionComplex X α V I).d n ((n : ℤ) + 1)) s.val) at h
  rw [s.property, map_zero] at h
  exact h

theorem moduleResolutionOpenSectionCyclesRestriction_apply (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α V I n) :
    (moduleResolutionOpenSectionCyclesRestriction X α i I n s).val =
      (I.cochainComplex.X n).presheaf.map i.op s.val := rfl

/-- Original section restriction is original precomposition by the native module-open map. -/
theorem moduleResolutionOpenSectionHom_restriction (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α V I n) :
    let ψ : Scheme.Modules.openFree X U ⟶ Scheme.Modules.openFree X V :=
      (Scheme.Modules.openFreeFunctor X).map i
    moduleResolutionOpenSectionHom X α U I n
        (moduleResolutionOpenSectionCyclesRestriction X α i I n s) =
      ψ ≫ moduleResolutionOpenSectionHom X α V I n s := by
  let ψ : Scheme.Modules.openFree X U ⟶ Scheme.Modules.openFree X V :=
    (Scheme.Modules.openFreeFunctor X).map i
  have h : (Scheme.Modules.openFreeHomAddEquiv X U (I.cochainComplex.X n)).symm
      ((I.cochainComplex.X n).presheaf.map i.op s.val) =
    ψ ≫ (Scheme.Modules.openFreeHomAddEquiv X V (I.cochainComplex.X n)).symm s.val := by
    apply (Scheme.Modules.openFreeHomAddEquiv X U _).injective
    rw [AddEquiv.apply_symm_apply]
    change _ = Scheme.Modules.openFreeHomEquiv X U _
      ((Scheme.Modules.openFreeFunctor X).map i ≫ _)
    rw [Scheme.Modules.openFreeHomEquiv_naturality_open]
    change _ = (I.cochainComplex.X n).presheaf.map i.op
      ((Scheme.Modules.openFreeHomAddEquiv X V _)
        ((Scheme.Modules.openFreeHomAddEquiv X V _).symm s.val))
    rw [AddEquiv.apply_symm_apply]
  dsimp only [moduleResolutionOpenSectionHom]
  change (Scheme.Modules.openFreeHomAddEquiv X U _).symm
    ((I.cochainComplex.X n).presheaf.map i.op s.val) ≫ _ = _
  rw [h, Category.assoc]

/-- Actual section restriction on classes is the original native `H'` presheaf restriction. -/
theorem moduleResolutionOpenSectionClass_restriction (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α V I n) :
    moduleHPrimeRestrictionOfHom X α M n i (moduleResolutionOpenSectionClass X α V I n s) =
      moduleResolutionOpenSectionClass X α U I n
        (moduleResolutionOpenSectionCyclesRestriction X α i I n s) := by
  change (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n).map i.op
      (moduleOpenExtCohomologyMap X V M n (moduleResolutionOpenSectionExtClass X α V I n s)) =
    moduleOpenExtCohomologyMap X U M n
      (moduleResolutionOpenSectionExtClass X α U I n
        (moduleResolutionOpenSectionCyclesRestriction X α i I n s))
  rw [← moduleOpenExtCohomologyMap_restriction X i M n]
  apply congrArg (moduleOpenExtCohomologyMap X U M n)
  rw [moduleResolutionOpenSectionExtClass_eq_extMk,
    moduleResolutionOpenSectionExtClass_eq_extMk, InjectiveResolution.mk₀_comp_extMk]
  congr 1
  exact (moduleResolutionOpenSectionHom_restriction X α i I n s).symm

/-- Native homology of the original open-section restriction is the unchanged open restriction
under the original cohomology comparison. -/
theorem moduleResolutionOpenSectionsCohomologyLinearEquiv_restriction (n : ℕ)
    (x : (moduleResolutionOpenSectionComplex X α V I).homology (n : ℤ)) :
    moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n
        (HomologicalComplex.homologyMap (moduleResolutionOpenSectionRestriction X α i I)
          (n : ℤ) x) =
      moduleHPrimeRestrictionOfHom X α M n i
        (moduleResolutionOpenSectionsCohomologyLinearEquiv X α V I n x) := by
  let K := moduleResolutionOpenSectionComplex X α V I
  let L := moduleResolutionOpenSectionComplex X α U I
  let a := moduleResolutionOpenSectionRestriction X α i I
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance) x
  have hπ := congrArg (fun k ↦ k c) (HomologicalComplex.homologyπ_naturality a (n : ℤ))
  change HomologicalComplex.homologyMap a (n : ℤ) (K.homologyπ n c) =
    L.homologyπ n (HomologicalComplex.cyclesMap a (n : ℤ) c) at hπ
  rw [hπ, moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ X α U I n,
    moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ X α V I n,
    moduleResolutionOpenSectionClass_restriction X α i I n]
  apply congrArg (moduleResolutionOpenSectionClass X α U I n)
  apply Subtype.ext
  rw [moduleResolutionOpenSectionCyclesIso_hom_val,
    moduleResolutionOpenSectionCyclesRestriction_apply,
    moduleResolutionOpenSectionCyclesIso_hom_val]
  exact congrArg (fun k ↦ k c) (HomologicalComplex.cyclesMap_i a (n : ℤ))

end Restriction

end AlgebraicGeometry.Scheme.Cohomology
