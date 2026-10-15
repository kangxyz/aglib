/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients

/-!
# Original top-open and whole-space resolution comparisons

The native identity on top sections compares the actual open-resolution
complex with the original global-section complex. Its homology map takes
the original open-cohomology class to the original whole-space class.
The normalization uses the canonical open-free-to-structure-module arrow.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {M : X.Modules} (I : InjectiveResolution M)

/-- The original identity on top sections, applied to the actual supplied resolution. -/
def moduleResolutionOpenTopSectionsIso :
    moduleResolutionOpenSectionComplex X α ⊤ I ≅ moduleResolutionSectionComplex X α I :=
  (NatIso.mapHomologicalComplex (moduleTopSectionsFunctorIso X α) (.up ℤ)).app I.cochainComplex

theorem moduleResolutionOpenTopSectionsIso_hom_f_apply (n : ℤ)
    (x : (moduleResolutionOpenSectionComplex X α ⊤ I).X n) :
    (moduleResolutionOpenTopSectionsIso X α I).hom.f n x = x := rfl

private theorem openFreeHom_top (P : X.Modules) (x : Γ(P, ⊤)) :
    (Scheme.Modules.openFreeHomAddEquiv X ⊤ P).symm x =
      moduleOpenTopUnitMap X ≫ (Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm x := by
  apply (Scheme.Modules.openFreeHomAddEquiv X ⊤ P).injective
  rw [AddEquiv.apply_symm_apply]
  change x = Scheme.Modules.openFreeHomEquiv X ⊤ P (_ ≫ _)
  rw [Scheme.Modules.openFreeHomEquiv_comp]
  change x = Scheme.Modules.Hom.app
    ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).symm x) ⊤
      ((Scheme.Modules.openFreeHomEquiv X ⊤ (SheafOfModules.unit X.ringCatSheaf))
        ((Scheme.Modules.openFreeHomEquiv X ⊤ _).symm (1 : Γ(X, ⊤))))
  rw [Equiv.apply_symm_apply]
  exact ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X P).apply_symm_apply x).symm

/-- The original top-section cycle class is the original global class after the native
whole-space cohomology identification. -/
theorem moduleResolutionOpenSectionClass_top (n : ℕ)
    (s : moduleResolutionOpenSectionCycles X α ⊤ I n) :
    sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) n
        (moduleResolutionOpenSectionClass X α ⊤ I n s) =
      moduleResolutionSectionClass X α I n ⟨s.val, s.property⟩ := by
  have hh : moduleResolutionOpenSectionHom X α ⊤ I n s =
      moduleOpenTopUnitMap X ≫
        moduleResolutionSectionHom X α I n ⟨s.val, s.property⟩ := by
    dsimp only [moduleResolutionOpenSectionHom, moduleResolutionSectionHom]
    rw [openFreeHom_top]
    exact Category.assoc _ _ _
  have he : moduleResolutionOpenSectionExtClass X α ⊤ I n s =
      (Ext.mk₀ (moduleOpenTopUnitMap X)).comp
        (moduleResolutionSectionExtClass X α I n ⟨s.val, s.property⟩) (Nat.zero_add n) := by
    rw [moduleResolutionOpenSectionExtClass_eq_extMk,
      moduleResolutionSectionExtClass_eq_extMk, InjectiveResolution.mk₀_comp_extMk]
    congr 1
  rw [moduleResolutionOpenSectionClass_apply, he, moduleOpenExtCohomologyMap_top]
  rfl

/-- The actual open-resolution comparison at the whole space is exactly the original
whole-space resolution comparison, with the native identity on top sections. -/
theorem moduleResolutionOpenSectionsCohomologyLinearEquiv_top (n : ℕ)
    (x : (moduleResolutionOpenSectionComplex X α ⊤ I).homology (n : ℤ)) :
    sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) n
        (moduleResolutionOpenSectionsCohomologyLinearEquiv X α ⊤ I n x) =
      moduleResolutionSectionsCohomologyLinearEquiv X α I n
        (homologyMap (moduleResolutionOpenTopSectionsIso X α I).hom (n : ℤ) x) := by
  let K := moduleResolutionOpenSectionComplex X α ⊤ I
  let a := (moduleResolutionOpenTopSectionsIso X α I).hom
  obtain ⟨c, rfl⟩ :=
    ((ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance) x
  have hπ := ConcreteCategory.congr_hom (homologyπ_naturality a (n : ℤ)) c
  change homologyMap a (n : ℤ) (K.homologyπ n c) =
    (moduleResolutionSectionComplex X α I).homologyπ n (cyclesMap a (n : ℤ) c) at hπ
  rw [hπ, moduleResolutionOpenSectionsCohomologyLinearEquiv_homologyπ,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ,
    moduleResolutionOpenSectionClass_top]
  apply congrArg (moduleResolutionSectionClass X α I n)
  apply Subtype.ext
  rw [moduleResolutionOpenSectionCyclesIso_hom_val, moduleResolutionSectionCyclesIso_hom_val]
  exact (ConcreteCategory.congr_hom (cyclesMap_i a (n : ℤ)) c).symm

end AlgebraicGeometry.Scheme.Cohomology
