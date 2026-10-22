/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Sections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Frames
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Native
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit

/-!
# The actual normal line of a regular-point blowup

The actual restricted kernel and its dual are supplied by the original chart frames.
This consumer compares their intrinsic transitions with native projective twisting
through the same fixed centre-over-P1 comparison. The original Laurent chart detects
the actual cocycle equality. The dual comparison retains the original tensor evaluation;
no comparison family is supplied as a premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.Blowup.IdealFrames

universe u

attribute [local instance] MvPolynomial.gradedAlgebra


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The original two parameter charts, indexed in the coefficient-ring universe. -/
def parameterCentreChart (i : ULift.{u} (Fin 2)) :
    Spec (.of (Polynomial (ResidueField A))) ⟶ centreScheme (maximalIdeal A) :=
  Fin.cases (firstCentreChart A hd) (fun _ => secondCentreChart A hd) i.down

/-- The zero index is the original first parameter chart. -/
theorem parameterCentreChart_zero :
    parameterCentreChart A hd (ULift.up 0) = firstCentreChart A hd := rfl

/-- The one index is the original second parameter chart. -/
theorem parameterCentreChart_one :
    parameterCentreChart A hd (ULift.up 1) = secondCentreChart A hd := rfl

instance parameterCentreChartIsOpenImmersion (i : ULift.{u} (Fin 2)) :
    IsOpenImmersion (parameterCentreChart A hd i) := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact inferInstanceAs (IsOpenImmersion (firstCentreChart A hd))
  · exact inferInstanceAs (IsOpenImmersion (secondCentreChart A hd))

/-- The actual two chart ranges on the actual inverse-image centre. -/
def conormalOpenCover (i : ULift.{u} (Fin 2)) := (parameterCentreChart A hd i).opensRange

/-- The original parameter charts cover the actual centre, through the fixed centre-fibre iso. -/
theorem conormalOpenCover_covers : iSup (conormalOpenCover A hd) = ⊤ := by
  apply top_unique
  intro x _
  let e := centreFibreIso (maximalIdeal A)
  have hc := fibreCharts_cover (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.2 (e.hom x)
  have hinv : e.inv (e.hom x) = x := by
    exact congrArg (fun f => f x) e.hom_inv_id
  rcases hc with ⟨y, hy⟩ | ⟨y, hy⟩
  · apply Opens.mem_iSup.mpr
    refine ⟨ULift.up 0, y, ?_⟩
    change firstCentreChart A hd y = x
    change e.inv (firstFibreChart A hd y) = x
    exact (congrArg e.inv hy).trans hinv
  · apply Opens.mem_iSup.mpr
    refine ⟨ULift.up 1, y, ?_⟩
    change secondCentreChart A hd y = x
    change e.inv (secondFibreChart A hd y) = x
    exact (congrArg e.inv hy).trans hinv

/-- The original actual conormal frame on each indexed polynomial chart. -/
def parameterConormalChartFrame (i : ULift.{u} (Fin 2)) :
    SheafOfModules.unit (Spec (.of (Polynomial (ResidueField A)))).ringCatSheaf ≅
      (Scheme.Modules.pullback (parameterCentreChart A hd i)).obj
        (centreConormalLine (maximalIdeal A)).val := by
  rcases i with ⟨i⟩
  exact Fin.cases
    (motive := fun n : Fin 2 =>
      SheafOfModules.unit (Spec (.of (Polynomial (ResidueField A)))).ringCatSheaf ≅
        (Scheme.Modules.pullback (parameterCentreChart A hd (ULift.up n))).obj
          (centreConormalLine (maximalIdeal A)).val)
    (conormalChartFrame (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
      (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
      (parameters_spec A hd).2.2.2.2.1)
    (fun _ => conormalChartFrame (maximalIdeal A) (secondParameter A hd) (firstParameter A hd)
      (Ideal.span_pair_comm.trans (parameters_spec A hd).2.2.1)
      (parameters_spec A hd).2.2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.2) i

/-- The zero frame retains the original first kernel frame as a whole isomorphism. -/
theorem parameterConormalChartFrame_zero :
    parameterConormalChartFrame A hd (ULift.up 0) =
      conormalChartFrame (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
        (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
        (parameters_spec A hd).2.2.2.2.1 := rfl

/-- The one frame retains the original opposite kernel frame as a whole isomorphism. -/
theorem parameterConormalChartFrame_one :
    parameterConormalChartFrame A hd (ULift.up 1) =
      conormalChartFrame (maximalIdeal A) (secondParameter A hd) (firstParameter A hd)
        (Ideal.span_pair_comm.trans (parameters_spec A hd).2.2.1)
        (parameters_spec A hd).2.2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.2 := rfl

/-- The actual kernel-derived frames transported to the original chart ranges. -/
def conormalRangeFrame (i : ULift.{u} (Fin 2)) :
    (centreConormalLine (maximalIdeal A)).val.over (conormalOpenCover A hd i) ≅
      SheafOfModules.unit ((centreScheme (maximalIdeal A)).ringCatSheaf.over
        (conormalOpenCover A hd i)) :=
  sectionwiseRangeFrame (X := centreScheme (maximalIdeal A))
    (parameterCentreChart A hd i)
    (centreConormalLine (maximalIdeal A)).val (parameterConormalChartFrame A hd i)

/-- The intrinsic conormal cocycle is constructed from the actual kernel-derived frames. -/
def conormalCocycle : UnitCocycle (conormalOpenCover A hd) :=
  LocalFrames.cocycle (X := centreScheme (maximalIdeal A))
    (conormalOpenCover A hd) (centreConormalLine (maximalIdeal A)).val
    (conormalRangeFrame A hd)

/-- Gluing the intrinsic parameter cocycle recovers the actual conormal line. -/
def conormalCocycleIso : (conormalCocycle A hd).sheaf ≅
    (centreConormalLine (maximalIdeal A)).val :=
  LocalFrames.sheafIso (X := centreScheme (maximalIdeal A))
    (conormalOpenCover A hd) (centreConormalLine (maximalIdeal A)).val
    (conormalRangeFrame A hd) (conormalOpenCover_covers A hd)

/-- The reconstruction preserves the original parameter-frame morphism on each actual open. -/
theorem conormalCocycleIso_hom_over (i : ULift.{u} (Fin 2)) :
    (SheafOfModules.overFunctor (centreScheme (maximalIdeal A)).ringCatSheaf
      (conormalOpenCover A hd i)).map (conormalCocycleIso A hd).hom =
      ((conormalCocycle A hd).localIso i).hom ≫ (conormalRangeFrame A hd i).inv :=
  LocalFrames.sheafIso_hom_over (X := centreScheme (maximalIdeal A))
    (conormalOpenCover A hd) (centreConormalLine (maximalIdeal A)).val
    (conormalRangeFrame A hd) (conormalOpenCover_covers A hd) i

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory TopologicalSpace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- The fixed native coordinate lift retains each original polynomial-P1 coordinate open. -/
theorem finUlift_preimage_coordinateOpen (i : Fin 2) :
    (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom ⁻¹ᵁ
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up i) =
      Proj.basicOpen (Scheme.ProjectiveLine.grading R) (MvPolynomial.X i) := by
  change (Proj.map (MvPolynomial.gradedRename R (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)) _) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
      (MvPolynomial.X (ULift.up i)) = _
  rw [Proj.map_preimage_basicOpen]
  simp only [MvPolynomial.gradedRename_apply, MvPolynomial.rename_X]
  rfl

/-- An isomorphism retains the original range of an open chart under inverse image. -/
theorem preimage_chartRange_of_iso {W X Y : Scheme.{u}} (j : W ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsIso f] : f ⁻¹ᵁ (j ≫ f).opensRange = j.opensRange := by
  ext x
  change (∃ y, (j ≫ f) y = f x) ↔ ∃ y, j y = x
  constructor
  · rintro ⟨y, hy⟩
    change f (j y) = f x at hy
    exact ⟨y, f.homeomorph.injective hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The same fixed centre-over-P1 comparison followed by the canonical coordinate-universe lift. -/
def centreOverIsoNativeProjectiveLine :
    Over.mk (centreStructureMap (maximalIdeal A)) ≅
      Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec (ResidueField A) (ULift.{u} (Fin 2))) :=
  centreOverIsoProjectiveP1 A hd ≪≫
    Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative (ResidueField A)

/-- The original centre map used for the native twisting sheaf comparison. -/
def nativeCentreComparison : centreScheme (maximalIdeal A) ⟶
    AlgebraicGeometry.ProjectiveSpace (ResidueField A) (ULift.{u} (Fin 2)) :=
  (centreOverIsoNativeProjectiveLine A hd).hom.left

instance nativeCentreComparisonIsIso : IsIso (nativeCentreComparison A hd) :=
  ((Over.forget _).mapIso (centreOverIsoNativeProjectiveLine A hd)).isIso_hom

/-- The native twisting comparison retains the actual quotient structural arrow. -/
theorem nativeCentreComparison_over :
    nativeCentreComparison A hd ≫
      AlgebraicGeometry.ProjectiveSpace.toSpec (ResidueField A) (ULift.{u} (Fin 2)) =
      centreStructureMap (maximalIdeal A) :=
  (centreOverIsoNativeProjectiveLine A hd).hom.w

/-- The inverse images of the native coordinate opens are the original actual parameter ranges. -/
theorem nativeCentreComparison_coordinatePreimage (i : ULift.{u} (Fin 2)) :
    nativeCentreComparison A hd ⁻¹ᵁ
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A) (ULift.{u} (Fin 2)) i =
      conormalOpenCover A hd i := by
  rcases i with ⟨i⟩
  change (centreOverIsoProjectiveP1 A hd).hom.left ⁻¹ᵁ
      ((AlgebraicGeometry.ProjectiveSpace.finUliftIso (ResidueField A) 2).hom ⁻¹ᵁ
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A)
          (ULift.{u} (Fin 2)) (ULift.up i)) = _
  rw [finUlift_preimage_coordinateOpen, ← Scheme.ProjectiveLine.chart_opensRange]
  fin_cases i
  · change (centreOverIsoProjectiveP1 A hd).hom.left ⁻¹ᵁ
      (Scheme.ProjectiveLine.chart (ResidueField A) 0).opensRange =
      (firstCentreChart A hd).opensRange
    have hr :
        (firstCentreChart A hd ≫ (centreOverIsoProjectiveP1 A hd).hom.left).opensRange =
          (Scheme.ProjectiveLine.chart (ResidueField A) 0).opensRange :=
      Opens.ext (congrArg (fun q : Spec (.of (Polynomial (ResidueField A))) ⟶
        Scheme.ProjectiveLine.projectiveP1 (ResidueField A) => Set.range q)
          (firstCentreChart_projectiveP1 A hd))
    exact (congrArg (fun V => (centreOverIsoProjectiveP1 A hd).hom.left ⁻¹ᵁ V) hr).symm.trans
      (preimage_chartRange_of_iso (firstCentreChart A hd) _)
  · change (centreOverIsoProjectiveP1 A hd).hom.left ⁻¹ᵁ
      (Scheme.ProjectiveLine.chart (ResidueField A) 1).opensRange =
      (secondCentreChart A hd).opensRange
    have hr :
        (secondCentreChart A hd ≫ (centreOverIsoProjectiveP1 A hd).hom.left).opensRange =
          (Scheme.ProjectiveLine.chart (ResidueField A) 1).opensRange :=
      Opens.ext (congrArg (fun q : Spec (.of (Polynomial (ResidueField A))) ⟶
        Scheme.ProjectiveLine.projectiveP1 (ResidueField A) => Set.range q)
          (secondCentreChart_projectiveP1 A hd))
    exact (congrArg (fun V => (centreOverIsoProjectiveP1 A hd).hom.left ⁻¹ᵁ V) hr).symm.trans
      (preimage_chartRange_of_iso (secondCentreChart A hd) _)

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open AlgebraicGeometry HomogeneousLocalization MvPolynomial

variable (R : Type u) [CommRing R]

/-- The original fraction X0/X1 is the opposite original affine-chart coordinate. -/
theorem projectiveTransitionFraction_eq :
    Away.mk (Scheme.ProjectiveLine.grading R)
        ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2)))
        1 (X (0 : Fin 2) ^ 2) (by simpa using (isHomogeneous_X R (0 : Fin 2)).pow 2) =
      Scheme.ProjectiveLine.overlapMap1 R (Scheme.ProjectiveLine.chartRatio R 1) := by
  apply HomogeneousLocalization.val_injective
  simp only [Scheme.ProjectiveLine.overlapMap1, Scheme.ProjectiveLine.chartRatio,
    HomogeneousLocalization.awayMap_mk, Away.val_mk,
    show (1 : Fin 2).rev = 0 from rfl, pow_one]
  congr 1
  ring

/-- Evaluation on the actual Laurent overlap sends the native transition fraction to T(-1). -/
theorem projectiveTransitionFraction_laurent :
    Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
      (Scheme.PolynomialLaurent.laurentCoordinateUnit (.of R))
      (Away.mk (Scheme.ProjectiveLine.grading R)
        ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2)))
        1 (X (0 : Fin 2) ^ 2) (by simpa using (isHomogeneous_X R (0 : Fin 2)).pow 2)) =
      LaurentPolynomial.T (-1) := by
  rw [projectiveTransitionFraction_eq, Scheme.ProjectiveLine.overlapValue_map1_ratio]
  rfl

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

/-- Two actual right inverse line bundles are compared by the proved tensor equivalence. -/
def rightDualComparison (X : Scheme.{u}) (L M N : LineBundle X)
    (eM : tensorSheaf X L.val M.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : tensorSheaf X L.val N.val ≅ SheafOfModules.unit X.ringCatSheaf) : M.val ≅ N.val :=
  (lineBundleDualTensorEquivalence X L).inverse.preimageIso (eM ≪≫ eN.symm)

/-- The comparison retains the original two evaluation isomorphisms as its exact tensor image. -/
theorem rightDualComparison_tensor_hom (X : Scheme.{u}) (L M N : LineBundle X)
    (eM : tensorSheaf X L.val M.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : tensorSheaf X L.val N.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    (lineBundleDualTensorEquivalence X L).inverse.map (rightDualComparison X L M N eM eN).hom =
      eM.hom ≫ eN.inv :=
  (lineBundleDualTensorEquivalence X L).inverse.map_preimage _

end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open Scheme.PolynomialLaurent

private theorem scheme_appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) : f.appLE ⊤ ⊤ h = f.appTop := by
  change f.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) = f.appTop
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem scheme_appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- Actual sections are detected on an open chart whose image is the displayed target open. -/
theorem appLE_injective_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : U = f ''ᵁ V) :
    Function.Injective (f.appLE U V e) := by
  subst U
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (f.appIso V).hom |>.injective

variable (R : Type u) [CommRing R]

/-- The actual homogeneous overlap chart is evaluated at the original Laurent coordinate. -/
def projectiveLaurentOverlap : Spec (.of (LaurentPolynomial R)) ⟶
    Scheme.ProjectiveLine.projectiveP1 R :=
  laurentPlus (.of R) ≫ Scheme.ProjectiveLine.chart R 0

/-- The original Laurent chart factors through the original homogeneous overlap fraction map. -/
theorem projectiveLaurentOverlap_factor :
    projectiveLaurentOverlap R =
      Spec.map (CommRingCat.ofHom (Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
        (laurentCoordinateUnit (.of R)))) ≫
        Proj.awayι (Scheme.ProjectiveLine.grading R)
          (X (0 : Fin 2) * X (1 : Fin 2))
          ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide) := by
  have hp : (Polynomial.aeval (LaurentPolynomial.T (1 : ℤ))).toRingHom =
      (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  have h0 : (Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
      (laurentCoordinateUnit (.of R))).comp (Scheme.ProjectiveLine.overlapMap0 R) =
      Scheme.ProjectiveLine.chartValue R (LaurentPolynomial R) 0 (LaurentPolynomial.T 1) :=
    RingHom.ext (Scheme.ProjectiveLine.overlapValue_map0 R (LaurentPolynomial R)
      (laurentCoordinateUnit (.of R)))
  rw [projectiveLaurentOverlap, Scheme.ProjectiveLine.chart, laurentPlus,
    ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent.comp (Scheme.ProjectiveLine.dehomogenize R 0))) ≫ _ = _
  rw [← hp]
  change Spec.map (CommRingCat.ofHom
      (Scheme.ProjectiveLine.chartValue R (LaurentPolynomial R) 0 (LaurentPolynomial.T 1))) ≫ _ = _
  rw [← h0, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Scheme.ProjectiveLine.overlapMap0, Proj.SpecMap_awayMap_awayι]

/-- The original homogeneous chart evaluates its original fraction section by the native
Spec global-section identification. -/
theorem projectiveOverlap_awayToSection_appLE
    (h : (⊤ : (Spec (.of (Scheme.ProjectiveLine.chartOverlapRing R))).Opens) ≤
      (Proj.awayι (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
        ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)) ⁻¹ᵁ
          Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))) :
    Proj.awayToSection (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2)) ≫
        (Proj.awayι (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
          ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)).appLE
            (Proj.basicOpen (Scheme.ProjectiveLine.grading R)
              (X (0 : Fin 2) * X (1 : Fin 2))) ⊤ h =
      (Scheme.ΓSpecIso (.of (Scheme.ProjectiveLine.chartOverlapRing R))).inv := by
  let U := Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
  let e := Proj.basicOpenIsoSpec (Scheme.ProjectiveLine.grading R)
    (X (0 : Fin 2) * X (1 : Fin 2))
    ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)
  have hi : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have hj :
      (Proj.awayι (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
        ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)).appLE
          U ⊤ h = U.topIso.inv ≫ e.inv.appTop := by
    change (e.inv ≫ U.ι).appLE U ⊤ h = _
    rw [← Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ (by simp) (by simp), hi,
      scheme_appLE_top]
  rw [hj]
  apply (cancel_epi (Scheme.ΓSpecIso (.of (Scheme.ProjectiveLine.chartOverlapRing R))).hom).mp
  have he : e.hom.appTop =
      (Scheme.ΓSpecIso (.of (Scheme.ProjectiveLine.chartOverlapRing R))).hom ≫
        Proj.awayToSection (Scheme.ProjectiveLine.grading R)
          (X (0 : Fin 2) * X (1 : Fin 2)) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top _ _
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by
      rw [he]
      simp only [Category.assoc]
    _ = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
    _ = _ := (Scheme.ΓSpecIso (.of (Scheme.ProjectiveLine.chartOverlapRing R))).hom_inv_id.symm


end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open Scheme.Modules.Invertible

variable (R : Type u) [CommRing R]

private theorem finiteFractionSections_congr
    {s t a b : MvPolynomial (Fin 2) R} (hst : s = t) (hab : a = b) {d n : ℕ}
    (hs : s ∈ homogeneousSubmodule (Fin 2) R d)
    (ht : t ∈ homogeneousSubmodule (Fin 2) R d)
    (ha : a ∈ homogeneousSubmodule (Fin 2) R (n • d))
    (hb : b ∈ homogeneousSubmodule (Fin 2) R (n • d))
    {V : (Scheme.ProjectiveLine.projectiveP1 R).Opens}
    (hVs : V ≤ Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s)
    (hVt : V ≤ Proj.basicOpen (homogeneousSubmodule (Fin 2) R) t) :
    sectionRestrict (Scheme.ProjectiveLine.projectiveP1 R) hVs
        ((Proj.awayToSection (homogeneousSubmodule (Fin 2) R) s).hom
          (Away.mk _ hs n a ha)) =
      sectionRestrict (Scheme.ProjectiveLine.projectiveP1 R) hVt
        ((Proj.awayToSection (homogeneousSubmodule (Fin 2) R) t).hom
          (Away.mk _ ht n b hb)) := by
  subst t b
  rfl

/-- Canonical coordinate lifting pulls the original lifted coordinate fraction back to
its original literal two-variable fraction, including the actual restriction maps. -/
theorem nativeCoordinateTransition_pullback
    {W : (AlgebraicGeometry.ProjectiveSpace R (ULift.{u} (Fin 2))).Opens}
    {V : (Scheme.ProjectiveLine.projectiveP1 R).Opens}
    (hi : W ≤ AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0))
    (hj : W ≤ AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1))
    (hV : V ≤ Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2)))
    (e : V ≤ (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom ⁻¹ᵁ W) :
    ((AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom.appLE W V e).hom
        (AlgebraicGeometry.ProjectiveSpace.coordinateTransitionOn R (ULift.{u} (Fin 2))
          (ULift.up 0) (ULift.up 1) hi hj :
            Γ(AlgebraicGeometry.ProjectiveSpace R (ULift.{u} (Fin 2)), W)) =
      sectionRestrict (Scheme.ProjectiveLine.projectiveP1 R) hV
        ((Proj.awayToSection (Scheme.ProjectiveLine.grading R)
          (X (0 : Fin 2) * X (1 : Fin 2))).hom
          (Away.mk (Scheme.ProjectiveLine.grading R)
            ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2)))
            1 (X (0 : Fin 2) ^ 2) (by simpa using (isHomogeneous_X R (0 : Fin 2)).pow 2))) := by
  let f := MvPolynomial.gradedRename R (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)
  let q := (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom
  let s : MvPolynomial (ULift.{u} (Fin 2)) R := X (ULift.up 0) * X (ULift.up 1)
  have hs : s ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) R (1 + 1) :=
    (isHomogeneous_X R (ULift.up 0)).mul (isHomogeneous_X R (ULift.up 1))
  have hW := AlgebraicGeometry.ProjectiveSpace.le_basicOpen_coordinate_mul R
    (ULift.{u} (Fin 2)) (ULift.up 0) (ULift.up 1) hi hj
  have hV' : V ≤ Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (f s) :=
    fun x hx => hW (e hx)
  let z := AlgebraicGeometry.ProjectiveSpace.coordinateOverlapRatio R
    (ULift.{u} (Fin 2)) (ULift.up 0) (ULift.up 1) (ULift.up 0)
  have h₁ := congrArg (fun g => g.hom
      ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s).hom z))
    (Scheme.Hom.map_appLE q e (homOfLE hW).op)
  have h₂ := congrArg (fun g => g.hom
      ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s).hom z))
    (Scheme.Hom.appLE_map q
      (le_rfl : Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (f s) ≤
        q ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s)
      (homOfLE hV').op)
  have h₃ :
      ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s ≫
        q.appLE (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s)
          (Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (f s)) le_rfl).hom) z =
      (Proj.awayToSection (homogeneousSubmodule (Fin 2) R) (f s)).hom (Away.map f s z) :=
    ConcreteCategory.congr_hom
      (Proj.awayToSection_comp_appLE f (MvPolynomial.irrelevant_le_map_gradedRename R
        (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)) hs) z
  change (q.appLE W V e).hom
      ((AlgebraicGeometry.ProjectiveSpace R (ULift.{u} (Fin 2))).presheaf.map
        (homOfLE hW).op |>.hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s).hom z)) = _
  refine h₁.trans (h₂.symm.trans ?_)
  change sectionRestrict (Scheme.ProjectiveLine.projectiveP1 R) hV'
      (((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s ≫
        q.appLE (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) R) s)
          (Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (f s)) le_rfl).hom) z) = _
  refine (congrArg (fun w => sectionRestrict (Scheme.ProjectiveLine.projectiveP1 R) hV' w)
    h₃).trans ?_
  dsimp only [z]
  rw [AlgebraicGeometry.ProjectiveSpace.coordinateOverlapRatio, Away.map_mk]
  exact finiteFractionSections_congr R
    (by simp [f, s, MvPolynomial.gradedRename_apply])
    (by simp [f, MvPolynomial.gradedRename_apply]) _ _ _ _ hV' hV

end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open Scheme.PolynomialLaurent Scheme.Modules.Invertible

variable (R : Type u) [CommRing R]

/-- The actual Laurent source evaluates the original homogeneous fraction section. -/
theorem projectiveLaurentOverlap_awayToSection_appLE
    (h : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤
      projectiveLaurentOverlap R ⁻¹ᵁ
        Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))) :
    Proj.awayToSection (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2)) ≫
        (projectiveLaurentOverlap R).appLE
          (Proj.basicOpen (Scheme.ProjectiveLine.grading R)
            (X (0 : Fin 2) * X (1 : Fin 2))) ⊤ h =
      CommRingCat.ofHom (Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
        (laurentCoordinateUnit (.of R))) ≫
          (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv := by
  let a := Proj.awayι (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
    ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)
  let U := Proj.basicOpen (Scheme.ProjectiveLine.grading R)
    (X (0 : Fin 2) * X (1 : Fin 2))
  let φ := CommRingCat.ofHom (Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
    (laurentCoordinateUnit (.of R)))
  have ha : (⊤ : (Spec (.of (Scheme.ProjectiveLine.chartOverlapRing R))).Opens) ≤ a ⁻¹ᵁ U := by
    rw [show U = a.opensRange from (Proj.opensRange_awayι _ _ _ _).symm,
      Scheme.Hom.preimage_opensRange]
  have ht : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤
      (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec (.of (Scheme.ProjectiveLine.chartOverlapRing R))).Opens) :=
    le_top
  have hf : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤
      (Spec.map φ ≫ a) ⁻¹ᵁ U :=
    ht.trans ((Spec.map φ).preimage_mono ha)
  rw [scheme_appLE_congr (projectiveLaurentOverlap_factor R) U ⊤ h hf,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map φ) a U ⊤ ⊤ ha ht,
    ← Category.assoc, projectiveOverlap_awayToSection_appLE, scheme_appLE_top]
  exact (Scheme.ΓSpecIso_inv_naturality φ).symm

/-- On the actual Laurent source the literal native fraction is the negative Laurent unit. -/
theorem projectiveTransitionSection_laurent
    (h : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤
      projectiveLaurentOverlap R ⁻¹ᵁ
        Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))) :
    ((projectiveLaurentOverlap R).appLE
      (Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))) ⊤ h)
      ((Proj.awayToSection (Scheme.ProjectiveLine.grading R)
        (X (0 : Fin 2) * X (1 : Fin 2)))
          (Away.mk (Scheme.ProjectiveLine.grading R)
            ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2)))
            1 (X (0 : Fin 2) ^ 2) (by simpa using (isHomogeneous_X R (0 : Fin 2)).pow 2))) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T (-1)) := by
  have H := ConcreteCategory.congr_hom
    (projectiveLaurentOverlap_awayToSection_appLE R h)
    (Away.mk (Scheme.ProjectiveLine.grading R)
      ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2)))
      1 (X (0 : Fin 2) ^ 2) (by simpa using (isHomogeneous_X R (0 : Fin 2)).pow 2))
  change _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
    (Scheme.ProjectiveLine.overlapValue R (LaurentPolynomial R)
      (laurentCoordinateUnit (.of R)) _) at H
  rw [projectiveTransitionFraction_laurent] at H
  exact H

end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Scheme.Modules.Invertible

private theorem transitionOn_full {X : Scheme.{u}} {ι : Type u}
    {U : ι → X.Opens} (c : UnitCocycle U) (i j : ι) :
    c.transitionOn i j inf_le_left inf_le_right = c.transition i j := by
  apply Units.ext
  exact sectionRestrict_refl X _ _

private theorem transitionOn_reverse {X : Scheme.{u}} {ι : Type u}
    {U : ι → X.Opens} (c : UnitCocycle U) (i j : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    c.transitionOn j i hj hi = (c.transitionOn i j hi hj)⁻¹ := by
  apply (mul_left_cancel (a := c.transitionOn i j hi hj))
  rw [c.transitionOn_cocycle i j i hi hj hi, c.transitionOn_self, mul_inv_cancel]

/-- A proved original pairwise transition equality retains its restriction on arbitrary
original common opens. This is only a map-coherence lemma, not a lifting hypothesis. -/
private theorem pullbackTransitionOn_of_transition
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u}
    {U : ι → Y.Opens} {U' : ι → X.Opens} (c : UnitCocycle U) (d : UnitCocycle U')
    (hU : ∀ i, f ⁻¹ᵁ U i = U' i) (i j : ι)
    (hij : ∀ e : U' i ⊓ U' j ≤ f ⁻¹ᵁ (U i ⊓ U j),
      Units.map (f.appLE (U i ⊓ U j) (U' i ⊓ U' j) e).hom.toMonoidHom
        (c.transition i j) = d.transition i j)
    {W : Y.Opens} {V : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (hi' : V ≤ U' i) (hj' : V ≤ U' j)
    (e : V ≤ f ⁻¹ᵁ W) :
    Units.map (f.appLE W V e).hom.toMonoidHom (c.transitionOn i j hi hj) =
      d.transitionOn i j hi' hj' := by
  apply Units.ext
  have h := congrArg (fun z : (Γ(X, U' i ⊓ U' j))ˣ =>
    sectionRestrict X (le_inf hi' hj') z.val)
      (hij (UnitCocycle.inf_le_preimage_inf hU i j))
  refine Eq.trans ?_ h
  change (Y.presheaf.map (homOfLE (le_inf hi hj)).op ≫ f.appLE W V e).hom
      (c.transition i j).val =
    (f.appLE (U i ⊓ U j) (U' i ⊓ U' j)
        (UnitCocycle.inf_le_preimage_inf hU i j) ≫
      X.presheaf.map (homOfLE (le_inf hi' hj')).op).hom (c.transition i j).val
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- On two original charts, a proved forward transition fixes the entire actual cocycle
pullback. The reverse and diagonal cases follow from the genuine unit-cocycle laws. -/
private theorem twoChart_transitionPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : ULift.{u} (Fin 2) → Y.Opens} {U' : ULift.{u} (Fin 2) → X.Opens}
    (c : UnitCocycle U) (d : UnitCocycle U')
    (hU : ∀ i, f ⁻¹ᵁ U i = U' i)
    (h01 : ∀ e : U' (ULift.up 0) ⊓ U' (ULift.up 1) ≤
        f ⁻¹ᵁ (U (ULift.up 0) ⊓ U (ULift.up 1)),
      Units.map (f.appLE (U (ULift.up 0) ⊓ U (ULift.up 1))
          (U' (ULift.up 0) ⊓ U' (ULift.up 1)) e).hom.toMonoidHom
        (c.transition (ULift.up 0) (ULift.up 1)) =
      d.transition (ULift.up 0) (ULift.up 1)) :
    UnitCocycle.TransitionPullback f c d := by
  intro i j e
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rw [← transitionOn_full, ← transitionOn_full,
      UnitCocycle.transitionOn_self, UnitCocycle.transitionOn_self, map_one]
  · exact h01 e
  · have h := pullbackTransitionOn_of_transition f c d hU (ULift.up 0) (ULift.up 1)
      h01 (V := U' (ULift.up 1) ⊓ U' (ULift.up 0))
      (W := U (ULift.up 1) ⊓ U (ULift.up 0))
      inf_le_right inf_le_left inf_le_right inf_le_left e
    rw [← transitionOn_full, ← transitionOn_full,
      transitionOn_reverse c, transitionOn_reverse d, map_inv]
    exact congrArg (fun z => z⁻¹) h
  · rw [← transitionOn_full, ← transitionOn_full,
      UnitCocycle.transitionOn_self, UnitCocycle.transitionOn_self, map_one]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MvPolynomial
open Scheme.Modules.Invertible Scheme.PolynomialLaurent

private theorem unitMap_appLE_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (h₁ : V ≤ g ⁻¹ᵁ U) (h₂ : W ≤ f ⁻¹ᵁ V) (z : Γ(Z, U)ˣ) :
    Units.map (f.appLE V W h₂).hom.toMonoidHom
        (Units.map (g.appLE U V h₁).hom.toMonoidHom z) =
      Units.map ((f ≫ g).appLE U W (h₂.trans (f.preimage_mono h₁))).hom.toMonoidHom z := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE f g U V W h₁ h₂) z.val

private theorem unitMap_appLE_map_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (z : Γ(Y, U)ˣ) :
    Units.map (f.appLE U V hf).hom.toMonoidHom z =
      Units.map (g.appLE U V hg).hom.toMonoidHom z := by
  subst g
  rfl

variable (R : Type u) [CommRing R]

/-- The actual Laurent parameter chart, followed by the fixed canonical coordinate lift. -/
def nativeLaurentOverlap : Spec (.of (LaurentPolynomial R)) ⟶
    AlgebraicGeometry.ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  projectiveLaurentOverlap R ≫ (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom

/-- The original Laurent parameter map factors through the actual homogeneous overlap. -/
theorem projectiveLaurentOverlap_preimage :
    (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤ projectiveLaurentOverlap R ⁻¹ᵁ
      Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2)) := by
  let a := Proj.awayι (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))
    ((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))) (by decide)
  have ha : a ⁻¹ᵁ Proj.basicOpen (Scheme.ProjectiveLine.grading R)
      (X (0 : Fin 2) * X (1 : Fin 2)) = ⊤ := by
    rw [show Proj.basicOpen (Scheme.ProjectiveLine.grading R)
        (X (0 : Fin 2) * X (1 : Fin 2)) = a.opensRange from
          (Proj.opensRange_awayι _ _ _ _).symm,
      Scheme.Hom.preimage_opensRange]
  rw [projectiveLaurentOverlap_factor, Scheme.Hom.comp_preimage]
  change ⊤ ≤ _ ⁻¹ᵁ (a ⁻¹ᵁ _)
  rw [ha, Scheme.Hom.preimage_top]

private theorem finiteOverlap_le_nativePreimage :
    Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2)) ≤
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom ⁻¹ᵁ
        (AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
          AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1)) := by
  rw [Scheme.Hom.preimage_inf, finUlift_preimage_coordinateOpen,
    finUlift_preimage_coordinateOpen, ← Proj.basicOpen_mul]

/-- The original Laurent source maps into the two original native coordinate opens. -/
theorem nativeLaurentOverlap_preimage :
    (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤ nativeLaurentOverlap R ⁻¹ᵁ
      (AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1)) :=
  (projectiveLaurentOverlap_preimage R).trans
    ((projectiveLaurentOverlap R).preimage_mono (finiteOverlap_le_nativePreimage R))

/-- The original native coordinate transition evaluates to the inverse Laurent unit. -/
theorem nativeCoordinateUnit_laurent
    (h : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤ nativeLaurentOverlap R ⁻¹ᵁ
      (AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1))) :
    Units.map ((nativeLaurentOverlap R).appLE _ ⊤ h).hom.toMonoidHom
        ((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle R (ULift.{u} (Fin 2))).transition
          (ULift.up 0) (ULift.up 1)) = (laurentGlobalUnit (.of R))⁻¹ := by
  apply Units.ext
  have hc := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE
      (projectiveLaurentOverlap R) (AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom
      (AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1))
      (Proj.basicOpen (Scheme.ProjectiveLine.grading R) (X (0 : Fin 2) * X (1 : Fin 2))) ⊤
      (finiteOverlap_le_nativePreimage R) (projectiveLaurentOverlap_preimage R))
    (AlgebraicGeometry.ProjectiveSpace.coordinateTransitionOn R (ULift.{u} (Fin 2))
      (ULift.up 0) (ULift.up 1) inf_le_left inf_le_right).val
  refine hc.symm.trans ?_
  change (projectiveLaurentOverlap R).appLE _ ⊤ (projectiveLaurentOverlap_preimage R)
      (((AlgebraicGeometry.ProjectiveSpace.finUliftIso R 2).hom.appLE _ _
        (finiteOverlap_le_nativePreimage R)).hom _) = _
  rw [nativeCoordinateTransition_pullback R inf_le_left inf_le_right le_rfl]
  change (projectiveLaurentOverlap R).appLE _ ⊤ (projectiveLaurentOverlap_preimage R)
      ((Proj.awayToSection (Scheme.ProjectiveLine.grading R)
        (X (0 : Fin 2) * X (1 : Fin 2))).hom _) = _
  exact projectiveTransitionSection_laurent R (projectiveLaurentOverlap_preimage R)

/-- The actual O(1) transition is therefore the positive original Laurent unit. -/
theorem nativePositiveTwistUnit_laurent
    (h : (⊤ : (Spec (.of (LaurentPolynomial R))).Opens) ≤ nativeLaurentOverlap R ⁻¹ᵁ
      (AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
        AlgebraicGeometry.ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (ULift.up 1))) :
    Units.map ((nativeLaurentOverlap R).appLE _ ⊤ h).hom.toMonoidHom
        (((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle R
          (ULift.{u} (Fin 2))).zpow (-1)).transition (ULift.up 0) (ULift.up 1)) =
      laurentGlobalUnit (.of R) := by
  rw [UnitCocycle.zpow_transition, zpow_neg_one, map_inv, nativeCoordinateUnit_laurent, inv_inv]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.PolynomialLaurent

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The original positive Laurent chart of the actual exceptional centre. -/
def conormalOverlapChart : Spec (.of (LaurentPolynomial (ResidueField A))) ⟶
    centreScheme (maximalIdeal A) :=
  conormalOverlapMap (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1

instance conormalOverlapChartIsOpenImmersion : IsOpenImmersion (conormalOverlapChart A hd) :=
  inferInstanceAs (IsOpenImmersion (laurentPlus (.of (ResidueField A)) ≫ firstCentreChart A hd))

/-- This original chart has exactly the original pairwise range intersection as its image. -/
theorem conormalOverlapChart_image :
    conormalOpenCover A hd (ULift.up 0) ⊓ conormalOpenCover A hd (ULift.up 1) =
      conormalOverlapChart A hd ''ᵁ ⊤ := by
  have H := originalOverlap_opensRange
    (laurentPlus (.of (ResidueField A))) (laurentMinus (.of (ResidueField A)))
    (firstCentreChart A hd) (secondCentreChart A hd)
    (centreCharts_isPullback (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
      (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
      (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
      (parameters_spec A hd).2.2.2.2.2.2)
  exact H.symm.trans (conormalOverlapChart A hd).image_top_eq_opensRange.symm

/-- The actual entire Laurent source lies over that original range intersection. -/
theorem conormalOverlapChart_preimage :
    (⊤ : (Spec (.of (LaurentPolynomial (ResidueField A)))).Opens) ≤
      conormalOverlapChart A hd ⁻¹ᵁ
        (conormalOpenCover A hd (ULift.up 0) ⊓ conormalOpenCover A hd (ULift.up 1)) :=
  (conormalOverlap_preimage (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.2).ge

private theorem localFrames_transition_value {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : X.Modules)
    (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))) (i j : ι) :
    ((LocalFrames.cocycle U M e).transition i j).val =
      rangeFrameCoefficient M (U i) (U j) (e i) (e j) (U i ⊓ U j)
        inf_le_left inf_le_right := by
  rw [rangeFrameCoefficient_eq]
  rfl

private theorem conormalCocycle_transition_coefficient :
    ((conormalCocycle A hd).transition (ULift.up 0) (ULift.up 1)).val =
      conormalOverlapCoefficient (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
        (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
        (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
        (parameters_spec A hd).2.2.2.2.2.2 := by
  have H := localFrames_transition_value (X := centreScheme (maximalIdeal A))
    (conormalOpenCover A hd) (centreConormalLine (maximalIdeal A)).val
    (conormalRangeFrame A hd) (ULift.up 0) (ULift.up 1)
  rw [conormalOverlapCoefficient_original]
  simpa only [conormalCocycle, conormalOverlapOpen, conormalRangeFrame, conormalOpenCover,
    parameterCentreChart_zero, parameterCentreChart_one,
    parameterConormalChartFrame_zero, parameterConormalChartFrame_one] using H

/-- The actual intrinsic transition evaluates to the original positive Laurent unit. -/
theorem conormalCocycle_transition_laurent :
    Units.map ((conormalOverlapChart A hd).appLE _ ⊤
        (conormalOverlapChart_preimage A hd)).hom.toMonoidHom
      ((conormalCocycle A hd).transition (ULift.up 0) (ULift.up 1)) =
      laurentGlobalUnit (.of (ResidueField A)) := by
  apply Units.ext
  change (conormalOverlapChart A hd).appLE _ ⊤ (conormalOverlapChart_preimage A hd)
      (((conormalCocycle A hd).transition (ULift.up 0) (ULift.up 1)).val) =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial (ResidueField A)))).inv (LaurentPolynomial.T 1)
  rw [conormalCocycle_transition_coefficient]
  exact conormalOverlapCoefficient_laurent (maximalIdeal A)
    (firstParameter A hd) (secondParameter A hd) (parameters_spec A hd).2.2.1
    (parameters_spec A hd).2.2.2.1 (parameters_spec A hd).2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.2

/-- The same fixed centre-over-P1 comparison preserves this original Laurent chart. -/
theorem conormalOverlapChart_native :
    conormalOverlapChart A hd ≫ nativeCentreComparison A hd =
      nativeLaurentOverlap (ResidueField A) := by
  change (laurentPlus (.of (ResidueField A)) ≫ firstCentreChart A hd) ≫
      ((centreOverIsoProjectiveP1 A hd).hom.left ≫
        (AlgebraicGeometry.ProjectiveSpace.finUliftIso (ResidueField A) 2).hom) =
    (laurentPlus (.of (ResidueField A)) ≫ Scheme.ProjectiveLine.chart (ResidueField A) 0) ≫
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso (ResidueField A) 2).hom
  rw [Category.assoc, ← Category.assoc (firstCentreChart A hd),
    firstCentreChart_projectiveP1, Category.assoc]

/-- The actual positive native twist and actual conormal transition agree on their
original common open, detected by the original Laurent open immersion. -/
theorem conormalCocycle_forward
    (e : conormalOpenCover A hd (ULift.up 0) ⊓ conormalOpenCover A hd (ULift.up 1) ≤
      nativeCentreComparison A hd ⁻¹ᵁ
        (AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A)
            (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
          AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A)
            (ULift.{u} (Fin 2)) (ULift.up 1))) :
    Units.map ((nativeCentreComparison A hd).appLE _ _ e).hom.toMonoidHom
        (((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
          (ULift.{u} (Fin 2))).zpow (-1)).transition (ULift.up 0) (ULift.up 1)) =
      (conormalCocycle A hd).transition (ULift.up 0) (ULift.up 1) := by
  let z := ((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
    (ULift.{u} (Fin 2))).zpow (-1)).transition (ULift.up 0) (ULift.up 1)
  let U := AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A)
      (ULift.{u} (Fin 2)) (ULift.up 0) ⊓
    AlgebraicGeometry.ProjectiveSpace.coordinateOpen (ResidueField A)
      (ULift.{u} (Fin 2)) (ULift.up 1)
  let V := conormalOpenCover A hd (ULift.up 0) ⊓ conormalOpenCover A hd (ULift.up 1)
  have ht : (⊤ : (Spec (.of (LaurentPolynomial (ResidueField A)))).Opens) ≤
      (conormalOverlapChart A hd ≫ nativeCentreComparison A hd) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]
    exact (conormalOverlapChart_preimage A hd).trans
      ((conormalOverlapChart A hd).preimage_mono e)
  have hcomp := unitMap_appLE_comp (conormalOverlapChart A hd) (nativeCentreComparison A hd)
    U V ⊤ e (conormalOverlapChart_preimage A hd) z
  have hmap := unitMap_appLE_map_congr (conormalOverlapChart_native A hd) U ⊤ ht
    (nativeLaurentOverlap_preimage (ResidueField A)) z
  have hnative := hcomp.trans (hmap.trans (nativePositiveTwistUnit_laurent
    (ResidueField A) (nativeLaurentOverlap_preimage (ResidueField A))))
  apply Units.ext
  apply appLE_injective_of_image_eq (conormalOverlapChart A hd) _ ⊤
    (conormalOverlapChart_preimage A hd) (conormalOverlapChart_image A hd)
  exact congrArg Units.val (hnative.trans (conormalCocycle_transition_laurent A hd).symm)

/-- The actual intrinsic kernel-frame cocycle is the actual pullback of the native
positive projective twist through the original centre-over-P1 comparison. -/
theorem conormalCocycle_isPullback :
    UnitCocycle.TransitionPullback (nativeCentreComparison A hd)
      ((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
        (ULift.{u} (Fin 2))).zpow (-1)) (conormalCocycle A hd) :=
  twoChart_transitionPullback (nativeCentreComparison A hd) _ _
    (nativeCentreComparison_coordinatePreimage A hd) (conormalCocycle_forward A hd)

end AlgebraicGeometry.Scheme.Blowup.RegularPoint


namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The actual restricted kernel is the pullback of the native positive twist through the
same fixed centre-over-P1 comparison and its canonical coordinate lift. -/
def centreConormalTwistingIso :
    (Scheme.Modules.pullback (nativeCentreComparison A hd)).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField A)
          (ULift.{u} (Fin 2)) 1) ≅
      (centreConormalLine (maximalIdeal A)).val :=
  (((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
      (ULift.{u} (Fin 2))).zpow (-1)).pullbackIso
        (nativeCentreComparison A hd) (conormalCocycle A hd)
        (nativeCentreComparison_coordinatePreimage A hd)
        (conormalCocycle_isPullback A hd)
        (AlgebraicGeometry.ProjectiveSpace.iSup_coordinateOpen_eq_top (ResidueField A)
          (ULift.{u} (Fin 2)))) ≪≫ conormalCocycleIso A hd

/-- The intrinsic reconstruction sends each original cocycle generator to the original
kernel-derived range generator. -/
theorem conormalCocycleIso_hom_generator (i : ULift.{u} (Fin 2))
    {V : (centreScheme (maximalIdeal A)).Opens} (hV : V ≤ conormalOpenCover A hd i) :
    (conormalCocycleIso A hd).hom.val.app (Opposite.op V)
        ((conormalCocycle A hd).generator i hV) =
      (conormalRangeFrame A hd i).inv.val.app
        (Opposite.op (Over.mk (homOfLE hV)))
          (1 : Γ(centreScheme (maximalIdeal A), V)) := by
  have h := congrArg (fun f => f.val.app (Opposite.op (Over.mk (homOfLE hV)))
      ((conormalCocycle A hd).generator i hV))
    (conormalCocycleIso_hom_over A hd i)
  change (conormalCocycleIso A hd).hom.val.app (Opposite.op V)
      ((conormalCocycle A hd).generator i hV) =
    (conormalRangeFrame A hd i).inv.val.app (Opposite.op (Over.mk (homOfLE hV)))
      ((conormalCocycle A hd).localSectionsEquiv i hV
        ((conormalCocycle A hd).generator i hV)) at h
  rw [UnitCocycle.localSectionsEquiv_generator] at h
  exact h

/-- The positive-twist comparison preserves the original pulled generator on every
actual parameter subopen, rather than only its isomorphism class. -/
theorem centreConormalTwistingIso_hom_generator (i : ULift.{u} (Fin 2))
    {V : (centreScheme (maximalIdeal A)).Opens} (hV : V ≤ conormalOpenCover A hd i) :
    (centreConormalTwistingIso A hd).hom.val.app (Opposite.op V)
        (((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
          (ULift.{u} (Fin 2))).zpow (-1)).pullbackGenerator
            (nativeCentreComparison A hd) i
            (hV.trans (nativeCentreComparison_coordinatePreimage A hd i).ge)) =
      (conormalRangeFrame A hd i).inv.val.app
        (Opposite.op (Over.mk (homOfLE hV)))
          (1 : Γ(centreScheme (maximalIdeal A), V)) := by
  change (conormalCocycleIso A hd).hom.val.app (Opposite.op V)
      (((((AlgebraicGeometry.ProjectiveSpace.coordinateUnitCocycle (ResidueField A)
        (ULift.{u} (Fin 2))).zpow (-1)).pullbackIso
          (nativeCentreComparison A hd) (conormalCocycle A hd)
          (nativeCentreComparison_coordinatePreimage A hd) (conormalCocycle_isPullback A hd)
          (AlgebraicGeometry.ProjectiveSpace.iSup_coordinateOpen_eq_top (ResidueField A)
            (ULift.{u} (Fin 2)))).hom.val.app (Opposite.op V)) _) = _
  rw [UnitCocycle.pullbackIso_hom_pullbackGenerator, conormalCocycleIso_hom_generator]

/-- Pulling the native multiplication of positive and negative twists back gives its
actual evaluation against the constructed conormal comparison. -/
def centreConormalNegativeTwistEvaluation :
    tensorSheaf (centreScheme (maximalIdeal A)) (centreConormalLine (maximalIdeal A)).val
      ((pullbackLineBundle (nativeCentreComparison A hd)
        (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField A)
          (ULift.{u} (Fin 2)) (-1))).val) ≅
      SheafOfModules.unit (centreScheme (maximalIdeal A)).ringCatSheaf :=
  tensorSheafIso _ (centreConormalTwistingIso A hd).symm (Iso.refl _) ≪≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso (nativeCentreComparison A hd)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField A)
        (ULift.{u} (Fin 2)) 1)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField A)
        (ULift.{u} (Fin 2)) (-1))).symm ≪≫
    (Scheme.Modules.pullback (nativeCentreComparison A hd)).mapIso
      (AlgebraicGeometry.ProjectiveSpace.twistingTensorIso (ResidueField A)
        (ULift.{u} (Fin 2)) 1 (-1) ≪≫
        eqToIso (congrArg (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField A)
          (ULift.{u} (Fin 2))) (show (1 : ℤ) + -1 = 0 by decide)) ≪≫
        AlgebraicGeometry.ProjectiveSpace.twistingZeroIso (ResidueField A)
          (ULift.{u} (Fin 2))) ≪≫
    pullbackUnitIso (nativeCentreComparison A hd)

/-- The restriction of the dual of the original kernel is the original negative twist,
through the same parameter-dependent comparison of actual schemes. -/
def centreNormalTwistingIso :
    (centreNormalLine (maximalIdeal A)).val ≅
      (Scheme.Modules.pullback (nativeCentreComparison A hd)).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField A)
          (ULift.{u} (Fin 2)) (-1)) :=
  rightDualComparison (centreScheme (maximalIdeal A))
    (centreConormalLine (maximalIdeal A)) (centreNormalLine (maximalIdeal A))
    (pullbackLineBundle (nativeCentreComparison A hd)
      (AlgebraicGeometry.ProjectiveSpace.twistingLineBundle (ResidueField A)
        (ULift.{u} (Fin 2)) (-1)))
    (centreNormalEvaluationIso (maximalIdeal A)) (centreConormalNegativeTwistEvaluation A hd)

/-- The actual normal comparison preserves its original evaluation with the kernel ideal. -/
theorem centreNormalTwistingIso_tensor_hom :
    (lineBundleDualTensorEquivalence (centreScheme (maximalIdeal A))
      (centreConormalLine (maximalIdeal A))).inverse.map (centreNormalTwistingIso A hd).hom =
      (centreNormalEvaluationIso (maximalIdeal A)).hom ≫
        (centreConormalNegativeTwistEvaluation A hd).inv :=
  rightDualComparison_tensor_hom _ _ _ _ _ _

/-- The same comparison stated directly on the literal polynomial projective line.
Its negative twist is the pullback of the native twist by the canonical coordinate lift. -/
def centreNormalProjectiveP1Iso :
    (centreNormalLine (maximalIdeal A)).val ≅
      (Scheme.Modules.pullback (centreOverIsoProjectiveP1 A hd).hom.left).obj
        ((Scheme.Modules.pullback
          (AlgebraicGeometry.ProjectiveSpace.finUliftIso (ResidueField A) 2).hom).obj
            (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField A)
              (ULift.{u} (Fin 2)) (-1))) :=
  centreNormalTwistingIso A hd ≪≫
    ((pullbackComp (centreOverIsoProjectiveP1 A hd).hom.left
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso (ResidueField A) 2).hom).app
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf (ResidueField A)
          (ULift.{u} (Fin 2)) (-1))).symm

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
