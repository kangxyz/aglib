/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Forget

/-!
# Original global twist sections and native Laurent H0

The original section augmentation identifies actual global sections with native Laurent
homology in degree zero. Its canonical zero-term embedding is exactly the original
restriction family followed by the existing coordinate Laurent section maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech HomologicalComplex Opposite
open MvPolynomial AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Original global sections identify with native Laurent H0 through the unchanged Cech
augmentation and the existing actual Laurent complex isomorphism. -/
def twistingGlobalSectionsLaurentZeroLinearEquiv (d : ℤ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := Module.compHom Γ(twistingSheaf R ι d, ⊤) α
    Γ(twistingSheaf R ι d, ⊤) ≃ₗ[R]
      (coordinateLaurentTupleComplex (ι := ι) R d).homology 0 := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := Module.compHom Γ(twistingSheaf R ι d, ⊤) α
  exact ((moduleTopSectionsIso (ProjectiveSpace R ι) α (twistingSheaf R ι d)).symm ≪≫
    (moduleCechH0Iso (ProjectiveSpace R ι) α (twistingSheaf R ι d)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0).mapIso
      (twistingCechLaurentIso R ι d)).toLinearEquiv

/-- The canonical embedding of the original Laurent H0 class is exactly the original
Cech augmentation followed by the original zero-term Laurent comparison. -/
theorem twistingGlobalSectionsLaurentZeroLinearEquiv_homologyZeroι (d : ℤ)
    (s : Γ(twistingSheaf R ι d, ⊤)) :
    CochainComplex.homologyZeroι (coordinateLaurentTupleComplex (ι := ι) R d)
        (twistingGlobalSectionsLaurentZeroLinearEquiv R ι d s) =
      (twistingCechLaurentIso R ι d).hom.f 0
        (cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
          (twistingStructuralSections R ι d) s) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let C := moduleCechComplex (ProjectiveSpace R ι) α (twistingSheaf R ι d) (coordinateOpen R ι)
  let L := twistingCechLaurentIso R ι d
  let y := (moduleCechH0Iso (ProjectiveSpace R ι) α (twistingSheaf R ι d)
    (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)).inv
      ((moduleTopSectionsIso (ProjectiveSpace R ι) α (twistingSheaf R ι d)).inv s)
  have hnat := ConcreteCategory.congr_hom (CochainComplex.homologyZeroι_naturality L.hom) y
  change CochainComplex.homologyZeroι (coordinateLaurentTupleComplex (ι := ι) R d)
      (homologyMap L.hom 0 y) = L.hom.f 0 (CochainComplex.homologyZeroι C y) at hnat
  have haug := ConcreteCategory.congr_hom
    (moduleCechH0Iso_inv_homologyZeroι (ProjectiveSpace R ι) α (twistingSheaf R ι d)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι))
    ((moduleTopSectionsIso (ProjectiveSpace R ι) α (twistingSheaf R ι d)).inv s)
  change CochainComplex.homologyZeroι C y =
    cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
      (twistingStructuralSections R ι d) s at haug
  exact hnat.trans (congrArg (fun z => L.hom.f 0 z) haug)

/-- Every zero-term component is the original restriction of the original section, in its
existing tuple Laurent coordinates. -/
theorem twistingGlobalSectionsLaurentZeroLinearEquiv_component (d : ℤ)
    (s : Γ(twistingSheaf R ι d, ⊤)) (a : Fin 1 → ι) :
    CochainComplex.homologyZeroι (coordinateLaurentTupleComplex (ι := ι) R d)
        (twistingGlobalSectionsLaurentZeroLinearEquiv R ι d s) a =
      twistingTupleSectionsLinearEquiv R ι d 0 a
        ((twistingSheaf R ι d).val.map (homOfLE le_top).op s) := by
  rw [twistingGlobalSectionsLaurentZeroLinearEquiv_homologyZeroι]
  change (twistingCechLaurentTermIso R ι d 0).hom
    (cechAugmentationZero (ProjectiveSpace R ι) (coordinateOpen R ι)
      (twistingStructuralSections R ι d) s) a = _
  rw [twistingCechLaurentTermIso_hom_apply]
  apply congrArg (twistingTupleSectionsLinearEquiv R ι d 0 a)
  exact ConcreteCategory.congr_hom
    (cechAugmentationZero_π (ProjectiveSpace R ι) (coordinateOpen R ι)
      (twistingStructuralSections R ι d) a) s

end AlgebraicGeometry.Scheme.Cohomology
