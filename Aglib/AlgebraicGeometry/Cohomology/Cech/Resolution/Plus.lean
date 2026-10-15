/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Exact
public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution

/-!
# The original module Cech zigzag in bounded-below complexes

The native zero extension retains both original augmentations. The section
map uses the native comparison between applying global sections to the actual
integer-indexed resolution and extending its nonnegative section complex.
Every map is natural in the original coefficient and every supplied resolution
lift; no additive-resolution replacement is used.
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

/-- The original Cech complex extended by zero, retaining its native lower bound. -/
def moduleCechComplexPlus (M : X.Modules) : CochainComplex.Plus (ModuleCat.{u} R) :=
  ⟨(moduleCechComplex X α M U).extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

variable {M : X.Modules} (I : InjectiveResolution M)

/-- The original first-quadrant total extended by zero, with its native lower bound. -/
def moduleCechTotalPlus : CochainComplex.Plus (ModuleCat.{u} R) :=
  ⟨((moduleCechResolution X α U I).total (.up ℕ)).extend ComplexShape.embeddingUpNat,
    0, inferInstance⟩

/-- The unchanged Cech augmentation into the total, extended by zero. -/
def moduleCechToTotalPlus : moduleCechComplexPlus X α U M ⟶ moduleCechTotalPlus X α U I :=
  ⟨HomologicalComplex.extendMap (moduleCechToTotal X α U I) ComplexShape.embeddingUpNat⟩

/-- The original nonnegative section complex extended by zero, retaining its lower bound. -/
def moduleResolutionSectionExtendedPlus : CochainComplex.Plus (ModuleCat.{u} R) :=
  ⟨(moduleResolutionSectionCocomplex X α I).extend ComplexShape.embeddingUpNat,
    0, inferInstance⟩

/-- The original comparison between sections of the extended resolution and extended sections. -/
def moduleResolutionSectionExtendIsoPlus :
    (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus ≅
      moduleResolutionSectionExtendedPlus X α I :=
  (CochainComplex.plus (ModuleCat.{u} R)).isoMk
    (I.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
      ComplexShape.embeddingUpNat)

/-- The original nonnegative section augmentation, extended by zero without any comparison. -/
def moduleResolutionSectionsToTotalExtendedPlus :
    moduleResolutionSectionExtendedPlus X α I ⟶ moduleCechTotalPlus X α U I :=
  ⟨HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
    ComplexShape.embeddingUpNat⟩

/-- Actual global sections of the actual integer-indexed module resolution map to the same
total, through the native comparison for extension by zero. -/
def moduleResolutionSectionsToTotalPlus :
    (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      moduleCechTotalPlus X α U I :=
  ⟨(I.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
      ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
      ComplexShape.embeddingUpNat⟩

theorem moduleResolutionSectionsToTotalPlus_eq :
    moduleResolutionSectionsToTotalPlus X α U I =
      (moduleResolutionSectionExtendIsoPlus X α I).hom ≫
        moduleResolutionSectionsToTotalExtendedPlus X α U I := rfl

theorem moduleResolutionSectionsToTotalPlus_hom :
    (moduleResolutionSectionsToTotalPlus X α U I).hom =
      (I.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
        ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
        ComplexShape.embeddingUpNat := rfl

/-- The extended original Cech map remains a quasi-isomorphism. -/
theorem moduleCechToTotalPlus_quasiIso [M.IsQuasicoherent]
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k))) :
    QuasiIso (moduleCechToTotalPlus X α U I).hom := by
  let := moduleCechToTotal_quasiIso X α U I haff
  exact inferInstanceAs
    (QuasiIso (HomologicalComplex.extendMap (moduleCechToTotal X α U I)
      ComplexShape.embeddingUpNat))

/-- The extended original section map remains a quasi-isomorphism for an open cover. -/
theorem moduleResolutionSectionsToTotalPlus_quasiIso (hcover : iSup U = ⊤) :
    QuasiIso (moduleResolutionSectionsToTotalPlus X α U I).hom := by
  let := moduleResolutionSectionsToTotal_quasiIso X α U I hcover
  exact inferInstanceAs
    (QuasiIso ((I.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
      ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
          ComplexShape.embeddingUpNat))

theorem moduleResolutionSectionsToTotalExtendedPlus_quasiIso (hcover : iSup U = ⊤) :
    QuasiIso (moduleResolutionSectionsToTotalExtendedPlus X α U I).hom := by
  let := moduleResolutionSectionsToTotal_quasiIso X α U I hcover
  exact inferInstanceAs
    (QuasiIso (HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
      ComplexShape.embeddingUpNat))

section Naturality

variable {U I} {N : X.Modules} {J : InjectiveResolution N} {f : M ⟶ N}

/-- The original structural-ring coefficient map, extended by zero. -/
def moduleCechComplexPlusMap (f : M ⟶ N) :
    moduleCechComplexPlus X α U M ⟶ moduleCechComplexPlus X α U N :=
  ⟨HomologicalComplex.extendMap ((moduleCechFunctor X α U).map f)
    ComplexShape.embeddingUpNat⟩

/-- The original total map of a supplied resolution lift, extended by zero. -/
def moduleCechTotalPlusMap (φ : InjectiveResolution.Hom I J f) :
    moduleCechTotalPlus X α U I ⟶ moduleCechTotalPlus X α U J :=
  ⟨HomologicalComplex.extendMap
    (HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ))
      ComplexShape.embeddingUpNat⟩

/-- Zero extension preserves the actual coefficient/column-augmentation square. -/
theorem moduleCechToTotalPlus_naturality (φ : InjectiveResolution.Hom I J f) :
    moduleCechComplexPlusMap X α (U := U) f ≫ moduleCechToTotalPlus X α U J =
      moduleCechToTotalPlus X α U I ≫ moduleCechTotalPlusMap X α φ := by
  apply ObjectProperty.hom_ext
  change HomologicalComplex.extendMap ((moduleCechFunctor X α U).map f)
      ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (moduleCechToTotal X α U J) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap (moduleCechToTotal X α U I) ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap
        (HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ))
          ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun g ↦ HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
    (moduleCechToTotal_naturality X α (U := U) φ)

/-- Zero extension and its native section comparison preserve the actual row-augmentation
square for every original resolution lift. -/
theorem moduleResolutionSectionsToTotalPlus_naturality
    (φ : InjectiveResolution.Hom I J f) :
    (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.map φ.mapPlus ≫
        moduleResolutionSectionsToTotalPlus X α U J =
      moduleResolutionSectionsToTotalPlus X α U I ≫ moduleCechTotalPlusMap X α φ := by
  have he := I.cocomplex.mapExtendIso_hom_naturality
    (moduleGlobalSectionsFunctorOfHom X α) ComplexShape.embeddingUpNat φ.hom
  have h := congrArg
    (fun g ↦ (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map g)
    (moduleResolutionSectionsToTotal_naturality X α (U := U) φ)
  simp only [Functor.map_comp] at h
  change HomologicalComplex.extendMap
      (((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex _).map φ.hom)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U J)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
      ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap
        (HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ))
          ComplexShape.embeddingUpNat at h
  apply ObjectProperty.hom_ext
  change ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap φ.hom ComplexShape.embeddingUpNat) ≫
        ((J.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
          ComplexShape.embeddingUpNat).hom ≫
          HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U J)
            ComplexShape.embeddingUpNat) =
    ((I.cocomplex.mapExtendIso (moduleGlobalSectionsFunctorOfHom X α)
      ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (moduleResolutionSectionsToTotal X α U I)
        ComplexShape.embeddingUpNat) ≫
      HomologicalComplex.extendMap
        (HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ))
          ComplexShape.embeddingUpNat
  rw [← Category.assoc, he, Category.assoc, h, ← Category.assoc]

end Naturality

end AlgebraicGeometry.Scheme.Cohomology
