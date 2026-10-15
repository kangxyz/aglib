/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual open-resolution homology computes original native open cohomology

Homology of sections on each open of the supplied actual module injective
resolution is linearly identified with the unchanged native `Sheaf.H'`.
The forward map is the original represented Ext class, exact scalar
forgetting and the original integer-open generator. Native cycles,
boundaries and homology projections retain their original section values.
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

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (U : X.Opens)
  {M : X.Modules} (I : InjectiveResolution M)

/-- Actual open-section cycles map linearly to the original native open cohomology. -/
def moduleResolutionOpenSectionClass (n : ℕ) :
    letI := moduleHPrimeModuleOfHom X α M n U
    moduleResolutionOpenSectionCycles X α U I n →ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U := by
  letI := Scheme.Modules.moduleCategoryLinearOfHom X α
  letI := moduleHPrimeModuleOfHom X α M n U
  let c : moduleResolutionOpenSectionCycles X α U I n →ₗ[R]
      Ext.{u + 1} (Scheme.Modules.openFree X U) M n := {
    __ := moduleResolutionOpenSectionExtClass X α U I n
    map_smul' := fun r s ↦ moduleResolutionOpenSectionExtClass_smul X α U I n r s }
  exact (moduleOpenExtCohomologyLinearEquiv X U α M n).toLinearMap.comp c

theorem moduleResolutionOpenSectionClass_apply (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionClass X α U I n s =
      moduleOpenExtCohomologyMap X U M n
        (moduleResolutionOpenSectionExtClass X α U I n s) := rfl

theorem moduleResolutionOpenSectionClass_surjective (n : ℕ) :
    Function.Surjective (moduleResolutionOpenSectionClass X α U I n) :=
  (moduleOpenExtCohomologyMap_bijective X U M n).2.comp
    (moduleResolutionOpenSectionExtClass_surjective X α U I n)

/-- Its kernel criterion is the original actual section-boundary equation. -/
theorem moduleResolutionOpenSectionClass_eq_zero_iff (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionClass X α U I n s = 0 ↔
      ∃ t : (moduleResolutionOpenSectionComplex X α U I).X ((n : ℤ) - 1),
        ((moduleResolutionOpenSectionComplex X α U I).d ((n : ℤ) - 1) n) t = s.val := by
  change (moduleOpenExtCohomologyAddEquiv X U M n)
    (moduleResolutionOpenSectionExtClass X α U I n s) = 0 ↔ _
  rw [(moduleOpenExtCohomologyAddEquiv X U M n).map_eq_zero_iff,
    moduleResolutionOpenSectionExtClass_eq_zero_iff]

theorem moduleResolutionOpenSectionClass_ker (n : ℕ) :
    letI := moduleHPrimeModuleOfHom X α M n U
    let K := moduleResolutionOpenSectionComplex X α U I
    LinearMap.ker (moduleResolutionOpenSectionClass X α U I n) =
      LinearMap.range (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatToCycles := by
  let := moduleHPrimeModuleOfHom X α M n U
  ext s
  rw [LinearMap.mem_ker, moduleResolutionOpenSectionClass_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩

/-- Native homology is the actual quotient of the original open-section cycles by boundaries. -/
def moduleResolutionOpenSectionHomologyIso (n : ℕ) :
    let K := moduleResolutionOpenSectionComplex X α U I
    K.homology (n : ℤ) ≅ (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.H := by
  let K := moduleResolutionOpenSectionComplex X α U I
  exact K.homologyIsoSc' ((n : ℤ) - 1) n ((n : ℤ) + 1) (by simp) (by simp) ≪≫
    (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatHomologyIso

/-- Homology of original resolution sections on any open is the original native `Sheaf.H'`,
with the original structural scalar actions. -/
def moduleResolutionOpenSectionsCohomologyLinearEquiv (n : ℕ) :
    letI := moduleHPrimeModuleOfHom X α M n U
    (moduleResolutionOpenSectionComplex X α U I).homology (n : ℤ) ≃ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U := by
  letI := moduleHPrimeModuleOfHom X α M n U
  let K := moduleResolutionOpenSectionComplex X α U I
  let q : (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.H ≃ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U :=
    (Submodule.quotEquivOfEq _ _ (moduleResolutionOpenSectionClass_ker X α U I n).symm).trans
      ((moduleResolutionOpenSectionClass X α U I n).quotKerEquivOfSurjective
        (moduleResolutionOpenSectionClass_surjective X α U I n))
  exact (moduleResolutionOpenSectionHomologyIso X α U I n).toLinearEquiv.trans q

/-- The quotient representative maps to its original actual Ext/forgetting class. -/
theorem moduleResolutionOpenSectionsCohomologyLinearEquiv_apply_mk (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α U I n) :
    moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n
        ((moduleResolutionOpenSectionHomologyIso X α U I n).inv (Submodule.Quotient.mk s)) =
      moduleResolutionOpenSectionClass X α U I n s := by
  let := moduleHPrimeModuleOfHom X α M n U
  change ((Submodule.quotEquivOfEq _ _ (moduleResolutionOpenSectionClass_ker X α U I n).symm).trans
      ((moduleResolutionOpenSectionClass X α U I n).quotKerEquivOfSurjective
        (moduleResolutionOpenSectionClass_surjective X α U I n)))
    ((moduleResolutionOpenSectionHomologyIso X α U I n).toLinearEquiv
      ((moduleResolutionOpenSectionHomologyIso X α U I n).toLinearEquiv.symm
        (Submodule.Quotient.mk s))) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (moduleResolutionOpenSectionClass X α U I n)
    (moduleResolutionOpenSectionClass_surjective X α U I n) s

/-- Native abstract cycles retain their original open-section values. -/
def moduleResolutionOpenSectionCyclesIso (n : ℕ) :
    (moduleResolutionOpenSectionComplex X α U I).cycles (n : ℤ) ≅
      ModuleCat.of R (moduleResolutionOpenSectionCycles X α U I n) :=
  (moduleResolutionOpenSectionComplex X α U I).cyclesIsoSc'
      ((n : ℤ) - 1) n ((n : ℤ) + 1) (by simp) (by simp) ≪≫
    ((moduleResolutionOpenSectionComplex X α U I).sc'
      ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatCyclesIso

theorem moduleResolutionOpenSectionCyclesIso_hom_val (n : ℕ)
    (c : (moduleResolutionOpenSectionComplex X α U I).cycles (n : ℤ)) :
    ((moduleResolutionOpenSectionCyclesIso X α U I n).hom c).val =
      (moduleResolutionOpenSectionComplex X α U I).iCycles n c := by
  let K := moduleResolutionOpenSectionComplex X α U I
  have h : (moduleResolutionOpenSectionCyclesIso X α U I n).hom ≫
      (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.i = K.iCycles n := by
    dsimp only [moduleResolutionOpenSectionCyclesIso, Iso.trans_hom]
    rw [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  exact congrArg (fun k ↦ k c) h

/-- The actual quotient comparison preserves the original native homology projection. -/
theorem moduleResolutionOpenSectionHomologyIso_π (n : ℕ) :
    let K := moduleResolutionOpenSectionComplex X α U I
    K.homologyπ n ≫ (moduleResolutionOpenSectionHomologyIso X α U I n).hom =
      (moduleResolutionOpenSectionCyclesIso X α U I n).hom ≫
        (K.sc' ((n : ℤ) - 1) n ((n : ℤ) + 1)).moduleCatLeftHomologyData.π := by
  dsimp only [moduleResolutionOpenSectionHomologyIso, moduleResolutionOpenSectionCyclesIso,
    Iso.trans_hom]
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
    ShortComplex.π_moduleCatCyclesIso_hom]
  rw [Category.assoc]

theorem moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ (n : ℕ)
    (c : (moduleResolutionOpenSectionComplex X α U I).cycles (n : ℤ)) :
    moduleResolutionOpenSectionsCohomologyLinearEquiv X α U I n
        ((moduleResolutionOpenSectionComplex X α U I).homologyπ n c) =
      moduleResolutionOpenSectionClass X α U I n
        ((moduleResolutionOpenSectionCyclesIso X α U I n).hom c) := by
  let K := moduleResolutionOpenSectionComplex X α U I
  let e := moduleResolutionOpenSectionHomologyIso X α U I n
  have h := congrArg (fun k ↦ k c) (moduleResolutionOpenSectionHomologyIso_π X α U I n)
  change e.hom (K.homologyπ n c) =
    Submodule.Quotient.mk ((moduleResolutionOpenSectionCyclesIso X α U I n).hom c) at h
  have h' : K.homologyπ n c =
      e.inv (Submodule.Quotient.mk ((moduleResolutionOpenSectionCyclesIso X α U I n).hom c)) := by
    apply e.toLinearEquiv.injective
    change e.toLinearEquiv (K.homologyπ n c) = e.toLinearEquiv
      (e.toLinearEquiv.symm
        (Submodule.Quotient.mk ((moduleResolutionOpenSectionCyclesIso X α U I n).hom c)))
    rw [LinearEquiv.apply_symm_apply]
    exact h
  rw [h']
  exact moduleResolutionOpenSectionsCohomologyLinearEquiv_apply_mk X α U I n _

end AlgebraicGeometry.Scheme.Cohomology
