/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.ScalarChart
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.RowCoordinates
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.DegreeOneAugmentationChart

/-!
# The original projective map on arbitrary scalar blowup charts

The concrete scalar ratio map satisfies the generic original framed-row formula.
The same finite family is compared with its polynomial Proj embedding through the
actual denominator augmentation. Cancelling that closed augmentation and using the
proved original denominator cover gives equality of the original scheme maps and
closedness with the original structure triangle. No flatness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TensorProduct HomogeneousLocalization
open MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction

/-- The actual chart frame constructed from the same retained original projection equation. -/
def chartFrameOfTriangle
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] {I : Ideal R} (B : BlowupDatum (affineCenter R I)) (a : I)
    (φ : affineBlowupAlgebra R I a →+* T)
    (t : Spec (.of T) ⟶ pullback B.map (Spec.algebraMap R S))
    (hth : ScalarChartCoordinates.ChartTriangleEq t
      (pullback.fst B.map (Spec.algebraMap R S))
      (Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)) :
    (Modules.pullback t).obj (affineLine (S := S) B) ≅
      SheafOfModules.unit (Spec (.of T)).ringCatSheaf :=
  chartFrame B a φ t hth.eq

private theorem framedFamily_coefficient_of_triangle
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] {I : Ideal R}
    (B : BlowupDatum (affineCenter R I)) (a : I)
    (φ : affineBlowupAlgebra R I a →+* T)
    (t : Spec (.of T) ⟶ pullback B.map (Spec.algebraMap R S))
    (htp : t ≫ pullback.snd B.map (Spec.algebraMap R S) = Spec.algebraMap S T)
    (hth : ScalarChartCoordinates.ChartTriangleEq t
      (pullback.fst B.map (Spec.algebraMap R S))
      (Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a))
    (D : (Spec (.of S)).Modules)
    (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf) {ι : Type u}
    (π : (∐ fun _ : ι => D) ⟶
      degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S))
    (χ : S ⊗[R] I →ₗ[S] T)
    (hχ : ∀ (s : S) (b : I), χ (s ⊗ₜ[R] b) = algebraMap S T s * φ (ratio R I a b))
    (i : ι) :
    pullbackSection t (pulledFramedFamily B D eD π i) ≫
      (chartFrameOfTriangle B a φ t hth).hom =
        IdealFrames.affineMultiplication T (χ (AffineRow.generators I S D eD π i)) :=
  framedFamily_coefficient_of_scalarExtension B a φ t htp hth.eq D eD π χ hχ i

section ScalarChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I)) (a : I)

local notation "C" => affineBlowupAlgebra R I a
local notation "T" => S ⊗[R] C

/-- The original denominator frame transported along the two proved scalar-chart projections. -/
def scalarChartFrame :
    (Modules.pullback (ScalarChartCoordinates.scalarChartToPullback I S a B)).obj
        (affineLine (S := S) B) ≅
      SheafOfModules.unit (Spec (.of T)).ringCatSheaf :=
  chartFrameOfTriangle B a (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom
    (ScalarChartCoordinates.scalarChartToPullback I S a B)
    (ScalarChartCoordinates.scalarChartToPullback_fst I S a B)

variable (D : (Spec (.of S)).Modules)
  (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
  {ι : Type u}
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S))

/-- The exact original indexed presentation row has the corresponding polynomial coefficients
in the actual scalar-extended saturated chart frame. -/
theorem scalarChart_original_row (i : ι) :
    pullbackSection (ScalarChartCoordinates.scalarChartToPullback I S a B)
        (pulledFramedFamily B D eD π i) ≫
      (scalarChartFrame (S := S) B a).hom =
        IdealFrames.affineMultiplication T
          (ScalarChartCoordinates.scalarRatioLinearMap I S a
            (AffineRow.generators I S D eD π i)) := by
  refine framedFamily_coefficient_of_triangle
    (R := R) (S := S) («T» := T) (I := I) B a
    (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom
    (ScalarChartCoordinates.scalarChartToPullback I S a B)
    (ScalarChartCoordinates.scalarChartToPullback_snd I S a B)
    (ScalarChartCoordinates.scalarChartToPullback_fst I S a B) D eD π
    (ScalarChartCoordinates.scalarRatioLinearMap I S a) ?_ i
  intro s b
  rw [ScalarChartCoordinates.scalarRatioLinearMap_tmul]
  change s ⊗ₜ[R] ratio R I a b =
    (s ⊗ₜ[R] (1 : C)) * ((1 : S) ⊗ₜ[R] ratio R I a b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end ScalarChart

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.CoordinateAugmentation

open AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

private theorem iso_middle_cancel {C : Type*} [Category C] {X Y Z U V : C}
    (a : X ⟶ Y) (e : Y ≅ Z) (b : Y ⟶ U) (c : U ⟶ V) :
    (a ≫ e.hom) ≫ (e.inv ≫ b) ≫ c = a ≫ b ≫ c := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem precomp_eq_of_eq {C : Type*} [Category C] {X Y Z : C}
    (f f' : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hf : f = f') (he : f' ≫ g = h) :
    f ≫ g = h :=
  (congrArg (fun k => k ≫ g) hf).trans he

section ScalarRees

variable {R S ι : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I)) (v : ι → S ⊗[R] I)
  (hv : Submodule.span S (Set.range v) = ⊤) (a : I) (u : ι →₀ S)
  (hu : Finsupp.linearCombination S v u = (1 : S) ⊗ₜ[R] a)

local notation "C" => affineBlowupAlgebra R I a
local notation "T" => S ⊗[R] C
local notation "G" => Away.scalarGrading R (reesAlgebra.grading I) S
local notation "α" => (1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a
local notation "hα" => Away.scalarDenominator_mem R (reesAlgebra.grading I) S
  (reesAlgebra.degreeOne_mem I a)
local notation "g" => (fun i => reesAlgebra.scalarDegreeOneMap I S (v i))
local notation "hg" => reesAlgebra.span_scalarDegreeOneMap I S v hv
local notation "hp" => reesAlgebra.baseChange_grading_one_pow I
local notation "c" => (fun i => ScalarChartCoordinates.scalarRatioLinearMap I S a (v i))

include hu

private theorem denominatorRelation : Finsupp.linearCombination S g u = α := by
  have h := congrArg (reesAlgebra.scalarDegreeOneMap I S) hu
  rw [Finsupp.apply_linearCombination] at h
  exact h

/-- After adding the actual original denominator coordinate, the polynomial embedding on its
actual scalar Rees chart is the standard affine chart of the same ratio family. -/
theorem scalarChart_native_augmentation :
    ScalarChartCoordinates.scalarChartToPullback I S a B ≫
        AffineEmbedding.embedding B S v hv ≫ embedding u =
      ProjectiveSpace.FromSections.AffineChart.map (algebraMap S T) c := by
  let := Away.scalarAlgebra S G α
  let E := ScalarChartCoordinates.scalarChartRingEquiv I S a
  have hc : ScalarChartCoordinates.scalarChartToPullback I S a B ≫
      AffineEmbedding.embedding B S v hv ≫ embedding u =
      ScalarChartCoordinates.scalarChartToProj I S a ≫
        Proj.DegreeOneEmbedding.embedding G g hg hp ≫ embedding u :=
    iso_middle_cancel (ScalarChartCoordinates.scalarChartToProj I S a)
      (AffineEmbedding.scalarReesIso B S)
      (Proj.DegreeOneEmbedding.embedding G g hg hp) (embedding u)
  exact hc.trans (precomp_eq_of_eq
    (ScalarChartCoordinates.scalarChartToProj I S a)
    (ScalarChartCoordinates.ringChartMap G α hα E)
    (Proj.DegreeOneEmbedding.embedding G g hg hp ≫ embedding u)
    (ProjectiveSpace.FromSections.AffineChart.map (algebraMap S T) c)
    (ScalarChartCoordinates.scalarChartToProj_eq I S a)
    (native_chart_augmentation u G g hg hp α
      (denominatorRelation v a u hu) hα E (algebraMap S T) c
      (ScalarChartCoordinates.scalarChartRingEquiv_base I S a)
      (fun i => ScalarChartCoordinates.scalarRatio_numerator I S a (v i))))

end ScalarRees

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.CoordinateAugmentation


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I))


variable (D : (Spec (.of S)).Modules)
  (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
  {ι : Type u} [Finite ι]
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S)) [Epi π]

/-- The projective map of the specified original framed quotient family. -/
def mapOfFramedPresentation : pullback B.map (Spec.algebraMap R S) ⟶ ProjectiveSpace S ι :=
  mapOfFiniteFamily (pullback.snd B.map (Spec.algebraMap R S)) (affineLine (S := S) B)
    (pulledTautologicalLine B (Spec.algebraMap R S)).property (pulledFramedFamily B D eD π)

@[reassoc]
theorem mapOfFramedPresentation_toSpec :
    mapOfFramedPresentation B D eD π ≫ ProjectiveSpace.toSpec S ι =
      pullback.snd B.map (Spec.algebraMap R S) :=
  mapOfFiniteFamily_toSpec (pullback.snd B.map (Spec.algebraMap R S)) (affineLine (S := S) B)
    (pulledTautologicalLine B (Spec.algebraMap R S)).property
    (pulledFramedFamily B D eD π)

private theorem scalarChart_original_augmentation (a : I) (u : ι →₀ S)
    (hcomb : u.sum (fun i r => algebraMap S (S ⊗[R] affineBlowupAlgebra R I a) r *
      ScalarChartCoordinates.scalarRatioLinearMap I S a
        (AffineRow.generators I S D eD π i)) = 1) :
    ScalarChartCoordinates.scalarChartToPullback I S a B ≫
        mapOfFramedPresentation B D eD π ≫ Augmentation.embedding u =
      AffineChart.map (algebraMap S (S ⊗[R] affineBlowupAlgebra R I a))
        (fun i => ScalarChartCoordinates.scalarRatioLinearMap I S a
          (AffineRow.generators I S D eD π i)) := by
  let T := S ⊗[R] affineBlowupAlgebra R I a
  let t := ScalarChartCoordinates.scalarChartToPullback I S a B
  let c : ι → T := fun i => ScalarChartCoordinates.scalarRatioLinearMap I S a
    (AffineRow.generators I S D eD π i)
  let s := pulledFramedFamily B D eD π
  let e := scalarChartFrame (S := S) B a
  let p := pullback.snd B.map (Spec.algebraMap R S)
  let L := affineLine (S := S) B
  let hL : IsLocallyRankOne (pullback B.map (Spec.algebraMap R S)) L :=
    (pulledTautologicalLine B (Spec.algebraMap R S)).property
  let U : (Spec (.of T)).Modules := Augmentation.unitModule T
  have hs (i : ι) : pulledFamily t s i ≫ e.hom = Augmentation.plainFamily c i :=
    (scalarChart_original_row B a D eD π i).trans
      (IdealFrames.affineMultiplication_eq_unitMul T (c i))
  let hplain : Epi (Sigma.desc (Augmentation.plainFamily c)) := by
    have he : (fun i => pulledFamily t s i ≫ e.hom) =
        Augmentation.plainFamily c := funext hs
    rw [← he]
    infer_instance
  let : Epi (Sigma.desc (Augmentation.plainFamily c)) := hplain
  let hU : IsLocallyRankOne (Spec (.of T)) U :=
    isLocallyRankOne_of_iso (Spec (.of T)) e
      (pullback_locallyRankOne t L hL)
  have hm : t ≫ mapOfFramedPresentation B D eD π =
      mapOfFiniteFamily (Spec.map (CommRingCat.ofHom (algebraMap S T))) U hU
        (Augmentation.plainFamily c) := by
    calc
      _ = mapOfFiniteFamily (t ≫ p) ((Modules.pullback t).obj L)
          (pullback_locallyRankOne t L hL) (pulledFamily t s) :=
        mapOfFiniteFamily_pullback t p L hL s
      _ = mapOfFiniteFamily (t ≫ p) U hU (Augmentation.plainFamily c) :=
        mapOfFiniteFamily_iso (t ≫ p) _ U _ hU (pulledFamily t s)
          (Augmentation.plainFamily c) e hs
      _ = _ := by rw [ScalarChartCoordinates.scalarChartToPullback_snd]
  rw [← Category.assoc, hm]
  exact Augmentation.plainFamily_map_augmentation (hepi := hplain)
    u (algebraMap S T) c hU hcomb

private theorem scalarChart_original_eq_native (a : I) :
    ScalarChartCoordinates.scalarChartToPullback I S a B ≫
        mapOfFramedPresentation B D eD π =
      ScalarChartCoordinates.scalarChartToPullback I S a B ≫
        AffineEmbedding.embedding B S (AffineRow.generators I S D eD π)
          (AffineRow.span_generators I S D eD π) := by
  obtain ⟨u, hu, hc⟩ := ScalarChartCoordinates.exists_denominator_combination I S
    (AffineRow.generators I S D eD π) (AffineRow.span_generators I S D eD π) a
  let : IsClosedImmersion (Augmentation.embedding u) :=
    Augmentation.embedding_isClosedImmersion u
  apply (cancel_mono (Augmentation.embedding u)).mp
  simp only [Category.assoc]
  exact (scalarChart_original_augmentation B D eD π a u hc).trans
    (CoordinateAugmentation.scalarChart_native_augmentation B
      (AffineRow.generators I S D eD π) (AffineRow.span_generators I S D eD π) a u hu).symm

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  (B : BlowupDatum (affineCenter R I))


variable (D : (Spec (.of S)).Modules)
  (eD : D ≅ SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
  {ι : Type u} [Finite ι]
  (π : (∐ fun _ : ι => D) ⟶ degreeOneModule (I := affineCenter R I) (Spec.algebraMap R S)) [Epi π]

/-- The actual projective map of the specified original framed quotient is the polynomial
embedding defined by its recovered full tensor generators. -/
theorem mapOfFramedPresentation_eq_embedding :
    mapOfFramedPresentation B D eD π =
      AffineEmbedding.embedding B S (AffineRow.generators I S D eD π)
        (AffineRow.span_generators I S D eD π) := by
  apply ScalarChartCoordinates.scalarChart_hom_ext I B
  intro a
  exact scalarChart_original_eq_native B D eD π a

/-- The specified original affine quotient map is closed, with its original finite coordinates. -/
theorem mapOfFramedPresentation_isClosedImmersion :
    IsClosedImmersion (mapOfFramedPresentation B D eD π) := by
  rw [mapOfFramedPresentation_eq_embedding]
  exact AffineEmbedding.embedding_isClosedImmersion B S _ _

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.OriginalRowRestriction
