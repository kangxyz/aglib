/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Plus

/-!
# Original module Cech complexes model installed derived global sections

The genuine module-valued Cech zigzag is localized and composed with the
installed derived-unit comparison for the supplied actual module injective
resolution. The forward map retains both original augmentations, the native
global-sections/zero-extension comparison, and the installed derived unit.
Coefficient naturality holds for every actual lift between module resolutions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {ι : Type u} (U : ι → X.Opens)

local instance moduleCechDerivedSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

local instance moduleCechDerivedTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

variable {M : X.Modules} (I : InjectiveResolution M)
  (hcover : iSup U = ⊤)
  (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k)))

include hcover in
theorem moduleResolutionSectionsToTotalPlus_isIso :
    IsIso (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) :=
  Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
    (moduleResolutionSectionsToTotalPlus_quasiIso X α U I hcover)

include hcover in
theorem moduleResolutionSectionsToTotalExtendedPlus_isIso :
    IsIso (DerivedCategory.Plus.Q.map
      (moduleResolutionSectionsToTotalExtendedPlus X α U I)) :=
  Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
    (moduleResolutionSectionsToTotalExtendedPlus_quasiIso X α U I hcover)

variable [M.IsQuasicoherent]

/-- Localizing the original two augmentations identifies Cech with actual resolution sections. -/
def moduleCechResolutionDerivedIso :
    DerivedCategory.Plus.Q.obj (moduleCechComplexPlus X α U M) ≅
      DerivedCategory.Plus.Q.obj
        ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
          I.cochainComplexPlus) := by
  let : IsIso (DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (moduleCechToTotalPlus_quasiIso X α U I haff)
  let : IsIso (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (moduleResolutionSectionsToTotalPlus_quasiIso X α U I hcover)
  exact asIso (DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I)) ≪≫
    (asIso (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I))).symm

/-- The localized Cech comparison retains the two original augmentation maps. -/
theorem moduleCechResolutionDerivedIso_hom :
    letI := moduleResolutionSectionsToTotalPlus_isIso X α U I hcover
    (moduleCechResolutionDerivedIso X α U I hcover haff).hom =
      DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I) ≫
        inv (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) := rfl

@[reassoc (attr := simp)]
theorem moduleCechResolutionDerivedIso_hom_comp :
    (moduleCechResolutionDerivedIso X α U I hcover haff).hom ≫
        DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I) =
      DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I) := by
  let : IsIso (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (moduleResolutionSectionsToTotalPlus_quasiIso X α U I hcover)
  rw [moduleCechResolutionDerivedIso_hom]
  simp

/-- The original integer-indexed structural-ring Cech complex represents the installed
derived global sections of the original coefficient single. -/
def moduleCechDerivedGlobalSectionsIso :
    DerivedCategory.Plus.Q.obj (moduleCechComplexPlus X α U M) ≅
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  moduleCechResolutionDerivedIso X α U I hcover haff ≪≫
    InjectiveResolution.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α) I

/-- The derived-object comparison factors through the original two augmentations and the
actual native injective-resolution derived-unit comparison. -/
theorem moduleCechDerivedGlobalSectionsIso_hom :
    letI := moduleResolutionSectionsToTotalPlus_isIso X α U I hcover
    (moduleCechDerivedGlobalSectionsIso X α U I hcover haff).hom =
      DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I) ≫
        inv (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) ≫
          (InjectiveResolution.rightDerivedFunctorPlusIso
            (moduleGlobalSectionsFunctorOfHom X α) I).hom := by
  simp only [moduleCechDerivedGlobalSectionsIso, Iso.trans_hom,
    moduleCechResolutionDerivedIso_hom, Category.assoc]

/-- Fully expanded forward map: the original extended Cech augmentation, inverse original
extended section augmentation, literal native section/extension comparison, and derived unit
model. -/
theorem moduleCechDerivedGlobalSectionsIso_hom_expanded :
    letI := moduleResolutionSectionsToTotalExtendedPlus_isIso X α U I hcover
    (moduleCechDerivedGlobalSectionsIso X α U I hcover haff).hom =
      DerivedCategory.Plus.Q.map (moduleCechToTotalPlus X α U I) ≫
        inv (DerivedCategory.Plus.Q.map
          (moduleResolutionSectionsToTotalExtendedPlus X α U I)) ≫
        DerivedCategory.Plus.Q.map (moduleResolutionSectionExtendIsoPlus X α I).inv ≫
        (InjectiveResolution.rightDerivedFunctorPlusIso
          (moduleGlobalSectionsFunctorOfHom X α) I).hom := by
  let : IsIso (DerivedCategory.Plus.Q.map
      (moduleResolutionSectionsToTotalExtendedPlus X α U I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (moduleResolutionSectionsToTotalExtendedPlus_quasiIso X α U I hcover)
  let := moduleResolutionSectionsToTotalPlus_isIso X α U I hcover
  have hδ : DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I) =
      DerivedCategory.Plus.Q.map (moduleResolutionSectionExtendIsoPlus X α I).hom ≫
        DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalExtendedPlus X α U I) := by
    rw [moduleResolutionSectionsToTotalPlus_eq, Functor.map_comp]
  have hi : inv (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U I)) =
      inv (DerivedCategory.Plus.Q.map
        (moduleResolutionSectionsToTotalExtendedPlus X α U I)) ≫
          DerivedCategory.Plus.Q.map (moduleResolutionSectionExtendIsoPlus X α I).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hδ, Category.assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [moduleCechDerivedGlobalSectionsIso_hom, hi]
  simp only [Category.assoc]

section Naturality

variable {I} {N : X.Modules} [N.IsQuasicoherent] {J : InjectiveResolution N} {f : M ⟶ N}

/-- Both original localized augmentations retain every actual coefficient-resolution lift. -/
@[reassoc]
theorem moduleCechResolutionDerivedIso_naturality (φ : InjectiveResolution.Hom I J f) :
    DerivedCategory.Plus.Q.map (moduleCechComplexPlusMap X α (U := U) f) ≫
        (moduleCechResolutionDerivedIso X α U J hcover haff).hom =
      (moduleCechResolutionDerivedIso X α U I hcover haff).hom ≫
        DerivedCategory.Plus.Q.map
          ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.map φ.mapPlus) := by
  let : IsIso (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U J)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _
      (moduleResolutionSectionsToTotalPlus_quasiIso X α U J hcover)
  apply (cancel_mono
    (DerivedCategory.Plus.Q.map (moduleResolutionSectionsToTotalPlus X α U J))).mp
  have hc := congrArg (fun g ↦ DerivedCategory.Plus.Q.map g)
    (moduleCechToTotalPlus_naturality X α (U := U) φ)
  have hr := congrArg (fun g ↦ DerivedCategory.Plus.Q.map g)
    (moduleResolutionSectionsToTotalPlus_naturality X α (U := U) φ)
  simp only [Functor.map_comp] at hc hr
  rw [Category.assoc, moduleCechResolutionDerivedIso_hom_comp, Category.assoc,
    hr, ← Category.assoc, moduleCechResolutionDerivedIso_hom_comp]
  exact hc

/-- The derived Cech model gives the installed derived coefficient map for every original
module morphism and every supplied lift between its actual module resolutions. -/
@[reassoc]
theorem moduleCechDerivedGlobalSectionsIso_naturality (φ : InjectiveResolution.Hom I J f) :
    DerivedCategory.Plus.Q.map (moduleCechComplexPlusMap X α (U := U) f) ≫
        (moduleCechDerivedGlobalSectionsIso X α U J hcover haff).hom =
      (moduleCechDerivedGlobalSectionsIso X α U I hcover haff).hom ≫
        (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f) := by
  simp only [moduleCechDerivedGlobalSectionsIso, Iso.trans_hom]
  rw [← Category.assoc, moduleCechResolutionDerivedIso_naturality X α U hcover haff φ,
    Category.assoc, InjectiveResolution.rightDerivedFunctorPlusIso_naturality,
    ← Category.assoc]

end Naturality

end AlgebraicGeometry.Scheme.Cohomology
