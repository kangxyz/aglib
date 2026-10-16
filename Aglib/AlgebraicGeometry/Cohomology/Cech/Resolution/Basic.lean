/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant

/-!
# Structural-ring Cech complexes of actual module resolutions

The bicomplex uses the supplied module injective resolution and the original
structural-ring section presheaf. Its two augmentations are the coefficient
inclusion and the original restriction augmentation. Actual global sections
are identified with presheaf sections at the top by the identity on elements.

Every construction is linear over the specified structural ring, and both
augmentations commute with every actual lift of a coefficient morphism.
No covering, affine, quasicoherent or flat hypothesis is needed here.
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

/-- The original structural-ring Cech construction, functorially in module coefficients. -/
abbrev moduleCechFunctor {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  moduleSectionsPresheafFunctor X α ⋙ cechComplexFunctor U

variable {ι : Type u} (U : ι → X.Opens) {M : X.Modules} (I : InjectiveResolution M)

/-- The Cech degree is the first degree; the second is the actual module resolution degree. -/
def moduleCechResolution : FirstQuadrant.{u, u} R :=
  HomologicalComplex₂.flip
    (((moduleCechFunctor X α U).mapHomologicalComplex _).obj I.cocomplex)

/-- The original nonnegative section complex of the supplied module resolution. -/
abbrev moduleResolutionSectionCocomplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex _).obj I.cocomplex

/-- Top-presheaf and native module section complexes agree by the original identity. -/
def moduleResolutionTopSectionsIso :
    ((Functor.mapHomologicalComplex
      (moduleSectionsPresheafFunctor X α ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)) _).obj I.cocomplex) ≅
      moduleResolutionSectionCocomplex X α I :=
  (NatIso.mapHomologicalComplex (moduleTopSectionsFunctorIso X α) _).app I.cocomplex

/-- Each row is augmented by the original restriction of top presheaf sections. -/
def moduleCechRowAugmentation :
    (SingleSecondZero R).obj
      ((Functor.mapHomologicalComplex
        (moduleSectionsPresheafFunctor X α ⋙
          (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)) _).obj I.cocomplex) ⟶
        (moduleCechResolution X α U I).flip where
  f q := moduleCechAugmentation X α (I.cocomplex.X q) U
  comm' i j _ :=
    (cechAugmentation_naturality X U
      ((moduleSectionsPresheafFunctor X α).map (I.cocomplex.d i j))).symm

theorem moduleCechResolutionAugmentationZero_d (p : ℕ) :
    ((moduleCechFunctor X α U).map (I.ι.f 0)).f p ≫
      ((moduleCechResolution X α U I).X p).d 0 1 = 0 := by
  change ((moduleCechFunctor X α U).map (I.ι.f 0)).f p ≫
    ((moduleCechFunctor X α U).map (I.cocomplex.d 0 1)).f p = 0
  rw [← comp_f, ← Functor.map_comp]
  have h : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by simp
  rw [h, Functor.map_zero, zero_f]

/-- Each column is augmented by the original coefficient-to-resolution inclusion. -/
def moduleCechColumnAugmentation :
    (SingleSecondZero R).obj (moduleCechComplex X α M U) ⟶
      moduleCechResolution X α U I where
  f p := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨((moduleCechFunctor X α U).map (I.ι.f 0)).f p,
      moduleCechResolutionAugmentationZero_d X α U I p⟩
  comm' i j _ := by
    apply from_single_hom_ext
    simp only [comp_f, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    exact ((moduleCechFunctor X α U).map (I.ι.f 0)).comm i j

@[simp] theorem moduleCechColumnAugmentation_f_zero (p : ℕ) :
    ((moduleCechColumnAugmentation X α U I).f p).f 0 =
      ((moduleCechFunctor X α U).map (I.ι.f 0)).f p := by
  simp [moduleCechColumnAugmentation]

/-- The actual Cech complex maps to the total through the original module resolution. -/
def moduleCechToTotal : moduleCechComplex X α M U ⟶
    (moduleCechResolution X α U I).total (.up ℕ) :=
  totalAugmentation (moduleCechColumnAugmentation X α U I)

/-- The actual global module-resolution sections map to the same native total. -/
def moduleResolutionSectionsToTotal : moduleResolutionSectionCocomplex X α I ⟶
    (moduleCechResolution X α U I).total (.up ℕ) :=
  (moduleResolutionTopSectionsIso X α I).inv ≫
    totalAugmentationFlip (moduleCechRowAugmentation X α U I)

theorem moduleCechToTotal_f (n : ℕ) :
    (moduleCechToTotal X α U I).f n =
      ((moduleCechFunctor X α U).map (I.ι.f 0)).f n ≫
        (moduleCechResolution X α U I).ιTotal (.up ℕ) n 0 n (Nat.add_zero n) := by
  simp [moduleCechToTotal]

theorem moduleResolutionSectionsToTotal_f (n : ℕ) :
    (moduleResolutionSectionsToTotal X α U I).f n =
      (moduleTopSectionsIso X α (I.cocomplex.X n)).inv ≫
        cechAugmentationZero X U (moduleSectionsPresheaf X α (I.cocomplex.X n)) ≫
          (moduleCechResolution X α U I).ιTotal (.up ℕ) 0 n n (Nat.zero_add n) := by
  simp [moduleResolutionSectionsToTotal, moduleCechRowAugmentation,
    moduleResolutionTopSectionsIso, moduleTopSectionsFunctorIso]

section Naturality

variable {U I} {N : X.Modules} {J : InjectiveResolution N} {f : M ⟶ N}

/-- The actual bicomplex map induced by a lift of the original coefficient map. -/
def moduleCechResolutionMap (φ : InjectiveResolution.Hom I J f) :
    moduleCechResolution X α U I ⟶ moduleCechResolution X α U J :=
  (flipFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ)).map
    (((moduleCechFunctor X α U).mapHomologicalComplex _).map φ.hom)

/-- The original restriction augmentation commutes with every supplied resolution lift. -/
theorem moduleCechRowAugmentation_naturality (φ : InjectiveResolution.Hom I J f) :
    (SingleSecondZero R).map
      ((Functor.mapHomologicalComplex
        (moduleSectionsPresheafFunctor X α ⋙
          (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)) _).map φ.hom) ≫
        moduleCechRowAugmentation X α U J =
      moduleCechRowAugmentation X α U I ≫
        (flipFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ)).map
          (moduleCechResolutionMap X α φ) := by
  ext q : 1
  exact cechAugmentation_naturality X U
    ((moduleSectionsPresheafFunctor X α).map (φ.hom.f q))

/-- The coefficient-to-resolution augmentation commutes with the original map and its lift. -/
theorem moduleCechColumnAugmentation_naturality (φ : InjectiveResolution.Hom I J f) :
    (SingleSecondZero R).map ((moduleCechFunctor X α U).map f) ≫
        moduleCechColumnAugmentation X α U J =
      moduleCechColumnAugmentation X α U I ≫ moduleCechResolutionMap X α φ := by
  ext p : 1
  apply from_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero, moduleCechColumnAugmentation_f_zero]
  change ((moduleCechFunctor X α U).map f).f p ≫
    ((moduleCechFunctor X α U).map (J.ι.f 0)).f p =
      ((moduleCechFunctor X α U).map (I.ι.f 0)).f p ≫
        ((moduleCechFunctor X α U).map (φ.hom.f 0)).f p
  rw [← comp_f, ← comp_f, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun g ↦ ((moduleCechFunctor X α U).map g).f p)
    φ.ι_f_zero_comp_hom_f_zero.symm

theorem moduleCechToTotal_naturality (φ : InjectiveResolution.Hom I J f) :
    (moduleCechFunctor X α U).map f ≫ moduleCechToTotal X α U J =
      moduleCechToTotal X α U I ≫
        HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ) :=
  totalAugmentation_naturality _ _ _ _ (moduleCechColumnAugmentation_naturality X α φ)

theorem moduleResolutionSectionsToTotal_naturality (φ : InjectiveResolution.Hom I J f) :
    ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex _).map φ.hom ≫
        moduleResolutionSectionsToTotal X α U J =
      moduleResolutionSectionsToTotal X α U I ≫
        HomologicalComplex₂.total.map (moduleCechResolutionMap X α φ) (.up ℕ) := by
  have h := totalAugmentationFlip_naturality _ _ _ _
    (moduleCechRowAugmentation_naturality X α (U := U) φ)
  have he :
      ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex _).map φ.hom ≫
          (moduleResolutionTopSectionsIso X α J).inv =
        (moduleResolutionTopSectionsIso X α I).inv ≫
          (Functor.mapHomologicalComplex
            (moduleSectionsPresheafFunctor X α ⋙
              (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)) _).map
                φ.hom :=
    (NatIso.mapHomologicalComplex (moduleTopSectionsFunctorIso X α) (.up ℕ)).inv.naturality
      φ.hom
  dsimp only [moduleResolutionSectionsToTotal]
  rw [← Category.assoc, he, Category.assoc, h, ← Category.assoc]

end Naturality

end AlgebraicGeometry.Scheme.Cohomology
