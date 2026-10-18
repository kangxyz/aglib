/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.Overlap
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# Actual global relative Euler sequence

The original actual chart arrows define matching sections of the original structure-linear
Hom sheaf. Native sheaf gluing and the original global Hom equivalence construct the actual
relative differential arrow to `O(-1) ⊗ π*V`, where `V` is the original degree-one polynomial
module. Its exact native restrictions are the original chart arrows, retaining the original
relative differential formula on every original ratio section.

The original augmentation completes a native short exact sequence, by the original polynomial
chart splittings and native open-cover detection of exactness. All commutative rings and
arbitrary coordinate types are supported, including empty and one-coordinate spaces.
Exactness is in the native category of module sheaves. Determinants, canonical lines and trace
normalization are subsequent owners.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original polynomial-spectrum coordinate charts jointly cover the original space. -/
theorem eulerPolynomialChart_cover :
    ∀ x : ProjectiveSpace R ι, ∃ (i : ι)
      (y : Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))),
        eulerPolynomialChart R ι i y = x := by
  intro x
  obtain ⟨i, hix⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
  let U := coordinateOpen R ι i
  let e := coordinateOpenIsoSpecPolynomial R ι i
  let x' : U.toScheme := ⟨x, hix⟩
  refine ⟨i, e.hom x', ?_⟩
  exact congrArg (fun f : U.toScheme ⟶ U.toScheme => (f ≫ U.ι) x') e.hom_inv_id

/-- Actual module morphisms on the original projective space are determined by their native
restrictions to the original polynomial charts. -/
theorem eulerPolynomialChart_hom_ext {M N : (ProjectiveSpace R ι).Modules}
    (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map f =
      (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map g) : f = g := by
  let H := InternalHom.sheaf (ProjectiveSpace R ι) M N
  let A : TopCat.Sheaf Ab (ProjectiveSpace R ι) := ⟨H.val.presheaf, H.isSheaf⟩
  apply (InternalHom.globalHomEquiv (ProjectiveSpace R ι) M N).injective
  apply A.eq_of_locally_eq' (fun i => (eulerPolynomialChart R ι i).opensRange) ⊤
    (fun _ => homOfLE le_top)
    (InternalHom.restrictionRanges_cover (X := ProjectiveSpace R ι)
      (fun i : ι => Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
      (eulerPolynomialChart R ι) (eulerPolynomialChart_cover R ι)).ge
  intro i
  exact (InternalHom.globalHomEquiv_restrict (X := ProjectiveSpace R ι)
    (eulerPolynomialChart R ι i) M N f).trans
    ((congrArg (InternalHom.restrictionHomEquiv (X := ProjectiveSpace R ι)
      (eulerPolynomialChart R ι i) M N) (h i)).trans
        (InternalHom.globalHomEquiv_restrict (X := ProjectiveSpace R ι)
          (eulerPolynomialChart R ι i) M N g).symm)

/-- The original actual chart arrow as an original section of the actual structure-linear Hom
sheaf on its original range. -/
def eulerDifferentialChartHomSection (i : ι) :
    Γ(InternalHom.sheaf (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι),
        (eulerPolynomialChart R ι i).opensRange) :=
  InternalHom.restrictionHomEquiv (X := ProjectiveSpace R ι) (eulerPolynomialChart R ι i)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι)
    (eulerDifferentialOnPolynomialChart R ι i)

/-- The literal native overlap equation gives a matching family in the original actual Hom
sheaf, with the original chart arrows as its sections. -/
theorem eulerDifferentialChartHomSection_compatible :
    TopCat.Presheaf.IsCompatible
      (InternalHom.sheaf (ProjectiveSpace R ι)
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
        (eulerMiddle R ι)).val.presheaf
      (fun i => (eulerPolynomialChart R ι i).opensRange)
      (eulerDifferentialChartHomSection R ι) := by
  intro i k
  exact InternalHom.restrictionHomSections_overlap (X := ProjectiveSpace R ι)
    (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι)
    (eulerDifferentialOnPolynomialChart R ι i) (eulerDifferentialOnPolynomialChart R ι k)
    (eulerDifferentialOnPolynomialChart_overlap R ι i k)

/-- The global section of the original Hom sheaf glued from the original actual chart arrows. -/
def eulerDifferentialHomSection :
    Γ(InternalHom.sheaf (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι),
        (⊤ : (ProjectiveSpace R ι).Opens)) := by
  let H := InternalHom.sheaf (ProjectiveSpace R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι)
  let A : TopCat.Sheaf Ab (ProjectiveSpace R ι) := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (fun i => (eulerPolynomialChart R ι i).opensRange)
    (⊤ : (ProjectiveSpace R ι).Opens) (fun _ => homOfLE le_top)
    (InternalHom.restrictionRanges_cover (X := ProjectiveSpace R ι)
      (fun i : ι => Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
      (eulerPolynomialChart R ι) (eulerPolynomialChart_cover R ι)).ge
    (eulerDifferentialChartHomSection R ι)
    (eulerDifferentialChartHomSection_compatible R ι)).choose

/-- Original restriction of the glued Hom section recovers the original actual chart arrow. -/
theorem eulerDifferentialHomSection_restrict (i : ι) :
    (InternalHom.sheaf (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
      (eulerMiddle R ι)).val.map (homOfLE
        (show (eulerPolynomialChart R ι i).opensRange ≤ ⊤ from le_top)).op
      (eulerDifferentialHomSection R ι) = eulerDifferentialChartHomSection R ι i := by
  let H := InternalHom.sheaf (ProjectiveSpace R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) (eulerMiddle R ι)
  let A : TopCat.Sheaf Ab (ProjectiveSpace R ι) := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (fun i => (eulerPolynomialChart R ι i).opensRange)
    (⊤ : (ProjectiveSpace R ι).Opens) (fun _ => homOfLE le_top)
    (InternalHom.restrictionRanges_cover (X := ProjectiveSpace R ι)
      (fun i : ι => Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
      (eulerPolynomialChart R ι) (eulerPolynomialChart_cover R ι)).ge
    (eulerDifferentialChartHomSection R ι)
    (eulerDifferentialChartHomSection_compatible R ι)).choose_spec.1 i

/-- The canonical actual global relative Euler differential arrow. -/
def eulerDifferential :
    Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι) ⟶ eulerMiddle R ι :=
  (InternalHom.globalHomEquiv (ProjectiveSpace R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
    (eulerMiddle R ι)).symm (eulerDifferentialHomSection R ι)

/-- Native restriction of the global Euler arrow is exactly the original actual chart arrow. -/
theorem eulerDifferential_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map (eulerDifferential R ι) =
      eulerDifferentialOnPolynomialChart R ι i := by
  apply (InternalHom.restrictionHomEquiv (X := ProjectiveSpace R ι) (eulerPolynomialChart R ι i)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
    (eulerMiddle R ι)).injective
  have hh := InternalHom.globalHomEquiv_restrict (X := ProjectiveSpace R ι)
    (eulerPolynomialChart R ι i)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
    (eulerMiddle R ι) (eulerDifferential R ι)
  simp only [eulerDifferential, Equiv.apply_symm_apply] at hh
  exact hh.symm.trans (eulerDifferentialHomSection_restrict R ι i)

/-- The original actual chart arrows uniquely characterize the global Euler arrow. -/
theorem eulerDifferential_unique
    (f : Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι) ⟶ eulerMiddle R ι)
    (hf : ∀ i, (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map f =
      eulerDifferentialOnPolynomialChart R ι i) : f = eulerDifferential R ι := by
  apply eulerPolynomialChart_hom_ext R ι
  intro i
  exact (hf i).trans (eulerDifferential_restrict R ι i).symm

/-- The actual global Euler arrow retains the original relative differential of each original
chart ratio on every native chart open. -/
theorem eulerDifferential_d_ratio (i j : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    (eulerDifferential R ι).val.app (op (eulerPolynomialChart R ι i ''ᵁ V))
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j (eulerPolynomialChart_image_le R ι i V))) =
      eulerKernelGenerator R ι i j (eulerPolynomialChart_image_le R ι i V) := by
  exact (congrArg (fun f => f.val.app (op V)
    ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
      (eulerCoordinateRatio R ι i j (eulerPolynomialChart_image_le R ι i V))))
        (eulerDifferential_restrict R ι i)).trans
          (eulerDifferentialOnPolynomialChart_d_ratio_any_open R ι i j V)


/-- The canonical actual global Euler arrows form a complex with the original augmentation. -/
theorem eulerDifferential_comp_augmentation :
    eulerDifferential R ι ≫ eulerAugmentation R ι = 0 := by
  apply eulerPolynomialChart_hom_ext R ι
  intro i
  apply (cancel_mono (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom).1
  rw [Functor.map_comp, eulerDifferential_restrict, Category.assoc, Functor.map_zero, zero_comp]
  exact eulerDifferentialOnPolynomialChart_comp_augmentation R ι i

/-- The actual global relative Euler short complex, retaining the original tensor orientation. -/
def eulerShortComplex : CategoryTheory.ShortComplex (ProjectiveSpace R ι).Modules :=
  CategoryTheory.ShortComplex.mk (eulerDifferential R ι) (eulerAugmentation R ι)
    (eulerDifferential_comp_augmentation R ι)

/-- The native restriction of the actual global complex is the original polynomial-chart
complex, with only the native restriction comparison of the original unit. -/
-- Retain the original restriction-isomorphism data head used by Euler exactness.
@[nolint defsWithUnderscore]
def eulerShortComplex_restrictIso (i : ι) :
    (eulerShortComplex R ι).map
      (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)) ≅
        eulerShortComplexOnPolynomialChart R ι i :=
  CategoryTheory.ShortComplex.isoMk
    (Iso.refl ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
      (eulerPolynomialChart R ι i)))
    (Iso.refl ((eulerMiddle R ι).restrict (eulerPolynomialChart R ι i)))
    (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i))
    (by
      change (𝟙 _) ≫ eulerDifferentialOnPolynomialChart R ι i =
        (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map
          (eulerDifferential R ι) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, eulerDifferential_restrict])
    (by
      change (𝟙 _) ≫ eulerAugmentationOnPolynomialChart R ι i =
        (Scheme.Modules.restrictFunctor (eulerPolynomialChart R ι i)).map
          (eulerAugmentation R ι) ≫
            (Scheme.Modules.restrictUnitIso (eulerPolynomialChart R ι i)).hom
      rw [Category.id_comp]
      rfl)

/-- The native actual relative Euler complex is short exact over every commutative ring, for
arbitrary coordinate types, including the empty space and the one-coordinate space. -/
theorem eulerShortComplex_shortExact : (eulerShortComplex R ι).ShortExact := by
  apply Scheme.Modules.shortExact_of_restrict_openCover
    (fun i : ι => Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
    (eulerPolynomialChart R ι) (eulerPolynomialChart_cover R ι)
  intro i
  exact CategoryTheory.ShortComplex.shortExact_of_iso
    (eulerShortComplex_restrictIso R ι i).symm
    (eulerShortComplexOnPolynomialChart_shortExact R ι i)

end AlgebraicGeometry.ProjectiveSpace
