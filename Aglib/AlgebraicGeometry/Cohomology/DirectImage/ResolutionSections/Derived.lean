/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients

/-!
# Homology of installed derived global sections and original cohomology

The actual bounded-below right-derived global-sections functor at the original
coefficient single computes the original additive `Sheaf.H`, linearly for the
specified structural ring map. The comparison retains the supplied module
injective resolution, its installed derived-unit comparison, native homology
factorization and original section-cycle class. It is natural for every actual
coefficient-resolution lift and independent of the supplied resolution.

No quasicoherence, flatness, Noetherianity or finiteness is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The standard derived-category structure on the indicated module category. -/
local instance derivedGlobalSectionsSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance derivedGlobalSectionsTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- Homology of the installed derived single is the actual resolution-section homology,
through the original derived-unit comparison and native localization factorization. -/
def moduleDerivedGlobalSectionsSingleResolutionIso {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≅
      (moduleResolutionSectionComplex X α I).homology (n : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
      (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) (n : ℤ)).app
      ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus)

/-- The forward arrow retains homology of the original model inverse and the native
localization/homology factorization. -/
theorem moduleDerivedGlobalSectionsSingleResolutionIso_hom {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    (moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) (n : ℤ)).hom.app
          ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
            I.cochainComplexPlus) := rfl

/-- Applying the original resolution model recovers the native homology factorization. -/
@[reassoc]
theorem moduleDerivedGlobalSectionsSingleResolutionIso_model_hom {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom ≫
      (moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom =
        (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) (n : ℤ)).hom.app
          ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
            I.cochainComplexPlus) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let e := H.mapIso (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α))
  change e.hom ≫ (e.inv ≫ _) = _
  exact e.hom_inv_id_assoc _

/-- The original supplied-resolution comparison preserves every actual coefficient lift. -/
@[reassoc]
theorem moduleDerivedGlobalSectionsSingleResolutionIso_hom_naturality
    {M N : X.Modules} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) ≫
      (moduleDerivedGlobalSectionsSingleResolutionIso X α J n).hom =
        (moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom ≫
          homologyMap
            (((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map
              φ.hom') (n : ℤ) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)
  let eI := H.mapIso (I.rightDerivedFunctorPlusIso F)
  let eJ := H.mapIso (J.rightDerivedFunctorPlusIso F)
  let PI := (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R)
    (n : ℤ)).app (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let PJ := (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R)
    (n : ℤ)).app (F.mapCochainComplexPlus.obj J.cochainComplexPlus)
  let q := H.map (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ.mapPlus))
  let d := H.map (F.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f))
  let t := homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := ModuleCat.{u} R) (n : ℤ)).hom.naturality (F.mapCochainComplexPlus.map φ.mapPlus)
  change q ≫ PJ.hom = PI.hom ≫ t at hP
  have hR := congrArg H.map (I.rightDerivedFunctorPlusIso_naturality F φ)
  simp only [Functor.map_comp] at hR
  change q ≫ eJ.hom = eI.hom ≫ d at hR
  have hR' : d ≫ eJ.inv = eI.inv ≫ q := by
    apply (cancel_mono eJ.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hR]
    simp only [Iso.inv_hom_id_assoc]
  change d ≫ (eJ.inv ≫ PJ.hom) = (eI.inv ≫ PI.hom) ≫ t
  rw [← Category.assoc, hR', Category.assoc, hP, Category.assoc]

/-- Homology of the installed derived global sections of the original coefficient single
is unchanged additive cohomology with its specified structural scalar action. -/
def moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleCohomologyModuleOfHom X α M n
  exact (moduleDerivedGlobalSectionsSingleResolutionIso X α I n).toLinearEquiv.trans
    (moduleResolutionSectionsCohomologyLinearEquiv X α I n)

/-- The original resolution-section comparison is the final factor of the forward map. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_apply {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (x) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n x =
      moduleResolutionSectionsCohomologyLinearEquiv X α I n
        ((moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom x) := rfl

/-- On the original supplied model, the comparison is exactly the existing section-homology
comparison after the native localization factorization. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_model {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ) (x) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom x) =
      moduleResolutionSectionsCohomologyLinearEquiv X α I n
        ((DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) (n : ℤ)).hom.app
          ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
            I.cochainComplexPlus) x) := by
  change moduleResolutionSectionsCohomologyLinearEquiv X α I n
    (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom ≫
      (moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom) x) = _
  rw [moduleDerivedGlobalSectionsSingleResolutionIso_model_hom]
  rfl

/-- The original abstract cycle projection gives its unchanged original Ext/cohomology class. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_homologyπ {M : X.Modules}
    (I : InjectiveResolution M) (n : ℕ)
    (c : (moduleResolutionSectionComplex X α I).cycles (n : ℤ)) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom
          ((DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) (n : ℤ)).inv.app
            ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
              I.cochainComplexPlus)
            ((moduleResolutionSectionComplex X α I).homologyπ (n : ℤ) c))) =
      moduleResolutionSectionClass X α I n
        ((moduleResolutionSectionCyclesIso X α I n).hom c) := by
  rw [moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_model]
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R)
    (n : ℤ)).app
      ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus)
  change moduleResolutionSectionsCohomologyLinearEquiv X α I n
    (P.toLinearEquiv (P.toLinearEquiv.symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I n c

/-- Every supplied native resolution lift gives the original cohomology coefficient map. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality
    {M N : X.Modules} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : InjectiveResolution.Hom I J f) (n : ℕ) (x) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α J n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) x) =
      moduleCohomologyMapOfHom X α f n
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n x) := by
  have h := congrArg (fun k => k x)
    (moduleDerivedGlobalSectionsSingleResolutionIso_hom_naturality X α φ n)
  change (moduleDerivedGlobalSectionsSingleResolutionIso X α J n).hom
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) x) =
    homologyMap
      (((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map φ.hom')
      (n : ℤ) ((moduleDerivedGlobalSectionsSingleResolutionIso X α I n).hom x) at h
  rw [moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_apply, h]
  exact moduleResolutionSectionsCohomologyLinearEquiv_naturality X α I J φ n _

/-- The comparison with original cohomology does not depend on the supplied resolution. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_eq {M : X.Modules}
    (I J : InjectiveResolution M) (n : ℕ) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n =
      moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α J n := by
  let φ : InjectiveResolution.Hom I J (𝟙 M) :=
    ⟨InjectiveResolution.desc (𝟙 M) J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero (𝟙 M) J I⟩
  ext x
  have h := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality X α φ n x
  have hid :
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map (𝟙 M))) = 𝟙 _ :=
    (DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map_id M
  rw [hid] at h
  change moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α J n x =
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (𝟙 M)) n
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n x) at h
  rw [(SheafOfModules.toSheaf X.ringCatSheaf).map_id M, Sheaf.H.map_id_apply] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Cohomology
