/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Gluing
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties

/-!
# The proper pinched line and its nodal cubic chart

The normalization gluing is compared by its actual charts to native projective
one-space. This proves properness of the pinched line. Its affine chart has
the literal cubic presentation, and its nonnormality prevents an isomorphism to P¹.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.PinchedLine

open Polynomial.PinchedPair

variable (k : Type u) [Field k]

namespace ProjectiveComparison
open Scheme.ProjectiveLine
variable (k : Type u) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localization of the polynomial chart away from `X - 1`, mapped to the affine line. -/
def infinityInclusion : Spec (.of (infinityChartRing k)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (infinityChartRing k)))
/-- The infinity chart ring defines an open subscheme of the affine polynomial line. -/
instance infinityInclusion_open : IsOpenImmersion (infinityInclusion k) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X - 1 : k[X])

/-- The restricted infinity chart mapped into the native projective line. -/
def restrictedInfinityChart : Spec (.of (infinityChartRing k)) ⟶ projectiveP1 k :=
  infinityInclusion k ≫ chart k 1
/-- The restricted infinity chart is open in the native projective line. -/
instance restrictedInfinityChart_open : IsOpenImmersion (restrictedInfinityChart k) :=
  IsOpenImmersion.comp _ _

lemma infinityInclusion_range :
    (infinityInclusion k).opensRange = PrimeSpectrum.basicOpen (Polynomial.X - 1 : k[X]) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (infinityChartRing k) _

lemma restrictedInfinityChart_range :
    (restrictedInfinityChart k).opensRange =
      Proj.basicOpen (grading k) (MvPolynomial.X 1) ⊓
        Proj.basicOpen (grading k) (MvPolynomial.X 0 - MvPolynomial.X 1) := by
  change (infinityInclusion k ≫ chart k 1).opensRange = _
  rw [Scheme.Hom.opensRange_comp, infinityInclusion_range]
  have hlin : (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ grading k 1 :=
    (MvPolynomial.isHomogeneous_X k 0).sub (MvPolynomial.isHomogeneous_X k 1)
  have hpre : chart k 1 ⁻¹ᵁ
      Proj.basicOpen (grading k) (MvPolynomial.X 0 - MvPolynomial.X 1) =
      PrimeSpectrum.basicOpen (Polynomial.X - 1 : k[X]) := by
    simpa [dehomogenizePolynomial] using chart_preimage_linear k 1 _ hlin
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, chart_opensRange]

lemma restrictedInfinityChart_preimage :
    chart k 0 ⁻¹ᵁ (restrictedInfinityChart k).opensRange =
      (normalizationOverlapInclusion k).opensRange := by
  rw [restrictedInfinityChart_range]
  change chart k 0 ⁻¹ᵁ _ =
    (Spec.map (CommRingCat.ofHom
      (algebraMap k[X] (Localization.Away (conductor k : k[X]))))).opensRange
  rw [Scheme.Hom.opensRange_localizationAway (R := .of k[X]) (conductor k : k[X])]
  have hlin : (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ grading k 1 :=
    (MvPolynomial.isHomogeneous_X k 0).sub (MvPolynomial.isHomogeneous_X k 1)
  rw [Scheme.Hom.preimage_inf, chart_preimage_linear k 0 _ (MvPolynomial.isHomogeneous_X k 1),
    chart_preimage_linear k 0 _ hlin]
  simp only [dehomogenizePolynomial, map_sub, MvPolynomial.eval₂Hom_X']
  change PrimeSpectrum.basicOpen (Polynomial.X : k[X]) ⊓
    PrimeSpectrum.basicOpen (1 - Polynomial.X : k[X]) = _
  rw [← PrimeSpectrum.basicOpen_mul]
  rw [show (Polynomial.X * (1 - Polynomial.X) : k[X]) = -(conductor k : k[X]) by
    change Polynomial.X * (1 - Polynomial.X) = -(Polynomial.X * (Polynomial.X - 1))
    ring]
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  exact not_congr (Ideal.neg_mem_iff x.asIdeal)

lemma restrictedCharts_cover (z : projectiveP1 k) :
    (∃ a, chart k 0 a = z) ∨ ∃ b, restrictedInfinityChart k b = z := by
  by_cases hz0 : z ∈ Proj.basicOpen (grading k) (MvPolynomial.X 0)
  · left
    rw [← chart_opensRange k 0] at hz0
    exact hz0
  right
  change z ∈ (restrictedInfinityChart k).opensRange
  rw [restrictedInfinityChart_range]
  have hz1 : z ∈ Proj.basicOpen (grading k) (MvPolynomial.X 1) := by
    have hc : z ∈ ⨆ i : Fin 2, Proj.basicOpen (grading k) (MvPolynomial.X i) := by
      rw [basicCharts_cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
    fin_cases i
    · exact False.elim (hz0 hi)
    · exact hi
  refine ⟨hz1, ?_⟩
  simp only [Proj.mem_basicOpen, not_not] at hz0 hz1 ⊢
  intro hd
  apply hz1
  have hh := z.asHomogeneousIdeal.toIdeal.sub_mem hz0 hd
  change MvPolynomial.X 1 ∈ z.asHomogeneousIdeal.toIdeal
  simpa only [sub_sub_cancel] using hh

lemma infinity_coordinate : gluingToInfinity k ≫ infinityInclusion k =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (ConductorReciprocal.invT k)).toRingHom) := by
  unfold gluingToInfinity canonicalInfinityOpen infinityOverlapInclusion infinityInclusion
  simp only [Category.assoc]
  change Spec.map (CommRingCat.ofHom (ConductorReciprocal.reciprocal k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (standardOverlapEquiv k).symm.toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (infinityChartRing k) (infinityOverlapRing k))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k[X] (infinityChartRing k))) = _
  simp only [Category.assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change ConductorReciprocal.reciprocal k
    ((standardOverlapEquiv k).symm
      (algebraMap (infinityChartRing k) (infinityOverlapRing k)
        (algebraMap k[X] (infinityChartRing k) p))) = _
  rw [← IsScalarTower.algebraMap_apply k[X] (infinityChartRing k) (infinityOverlapRing k),
    AlgEquiv.commutes]
  exact ConductorReciprocal.reciprocal_algebraMap k p

lemma lineChart_comm : normalizationOverlapInclusion k ≫ chart k 0 =
    gluingToInfinity k ≫ restrictedInfinityChart k := by
  let u : (normalizationOverlapRing k)ˣ :=
    ⟨ConductorReciprocal.t k, ConductorReciprocal.invT k,
      ConductorReciprocal.t_mul_invT k, ConductorReciprocal.invT_mul_t k⟩
  have h := chart_transition k (normalizationOverlapRing k) u
  have heval : (Polynomial.aeval (ConductorReciprocal.t k)).toRingHom =
      algebraMap k[X] (normalizationOverlapRing k) := by
    have hφ : Polynomial.aeval (algebraMap k[X] (ConductorReciprocal.W k) Polynomial.X) =
        IsScalarTower.toAlgHom k k[X] (ConductorReciprocal.W k) := by
      apply Polynomial.algHom_ext
      simp
    change (Polynomial.aeval (algebraMap k[X] (ConductorReciprocal.W k) Polynomial.X)).toRingHom =
      (IsScalarTower.toAlgHom k k[X] (ConductorReciprocal.W k)).toRingHom
    exact congrArg AlgHom.toRingHom hφ
  change Spec.map (CommRingCat.ofHom (Polynomial.aeval (ConductorReciprocal.t k)).toRingHom) ≫
      chart k 0 = Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (ConductorReciprocal.invT k)).toRingHom) ≫ chart k 1 at h
  rw [heval] at h
  rw [restrictedInfinityChart, ← Category.assoc, infinity_coordinate]
  exact h

/-- The normalization gluing mapped to the native projective line by its two charts. -/
def lineToP1 : lineGluing k ⟶ projectiveP1 k :=
  pushout.desc (chart k 0) (restrictedInfinityChart k) (lineChart_comm k)

/-- The chartwise comparison from the normalization gluing to the native projective line is an
isomorphism. -/
instance lineToP1_isIso : IsIso (lineToP1 k) :=
  OpenPushoutIso.desc_isIso (normalizationOverlapInclusion k) (gluingToInfinity k)
    (chart k 0) (restrictedInfinityChart k) (lineChart_comm k)
    (restrictedInfinityChart_preimage k) (restrictedCharts_cover k)

lemma lineToP1_over : lineToP1 k ≫ structureMap k = lineStructure k := by
  apply pushout.hom_ext
  · rw [← Category.assoc, lineToP1, pushout.inl_desc, lineStructure, pushout.inl_desc,
      chart_over]
  · rw [← Category.assoc, lineToP1, pushout.inr_desc, lineStructure, pushout.inr_desc,
      restrictedInfinityChart, Category.assoc, chart_over]
    exact Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom k k[X] (infinityChartRing k))

/-- The named canonical isomorphism to the actual projective-line scheme. -/
def lineIsoP1 : lineGluing k ≅ projectiveP1 k := asIso (lineToP1 k)

@[reassoc] theorem lineIsoP1_over :
    (lineIsoP1 k).hom ≫ structureMap k = lineStructure k := lineToP1_over k

/-- The normalization gluing is proper over `k`. -/
instance lineStructure_proper : IsProper (lineStructure k) := by
  have h : IsProper (lineToP1 k ≫ structureMap k) := inferInstance
  rwa [lineToP1_over] at h

/-- The pinched line is proper over `k`. -/
instance pinchedStructure_proper : IsProper (pinchedStructure k) := by
  have : UniversallyClosed (gluedNormalizationMap k ≫ pinchedStructure k) := by
    rw [gluedNormalizationMap_over]
    infer_instance
  have : UniversallyClosed (pinchedStructure k) :=
    UniversallyClosed.of_comp_surjective (gluedNormalizationMap k) (pinchedStructure k)
  exact { }

end ProjectiveComparison

/-- Affine normal stalks imply integral closedness of the actual coordinate ring. -/
private theorem integrallyClosed_of_affine_normalStalks (A : Type u) [CommRing A] [IsDomain A]
    (h : _root_.AlgebraicGeometry.Scheme.NormalStalks (Spec (.of A))) : IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hm
  let x : Spec (.of A) := ⟨p, inferInstance⟩
  let : IsIntegrallyClosed ((structurePresheafInCommRingCat A).stalk x) := (h x).2
  exact IsIntegrallyClosed.of_equiv (StructureSheaf.stalkIso A x).toRingEquiv.symm


/-- Normal stalks are transported along an actual scheme isomorphism. -/
private theorem normalStalks_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : _root_.AlgebraicGeometry.Scheme.NormalStalks Y) :
      _root_.AlgebraicGeometry.Scheme.NormalStalks X := by
  intro x
  have hx := h (e.hom x)
  let := hx.1
  let := hx.2
  let r := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨r.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv r⟩
section NonNormality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (k : Type u) [Field k]

/-- The actual proper pinched curve is not normal: its affine node chart is not
integrally closed. This conclusion does not use smooth-field normality. -/
theorem pinchedGluing_not_normal : ¬ _root_.AlgebraicGeometry.Scheme.NormalStalks (pinchedGluing
  k) := by
  intro h
  apply nodeRing_not_integrallyClosed k
  apply integrallyClosed_of_affine_normalStalks
  intro x
  let i := pushout.inl (gluingToNode k) (gluingToInfinity k)
  have hx := h (i x)
  let := hx.1
  let := hx.2
  let e := (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- Nonsmoothness follows from the existing universal smooth-field normality
foundation, not from an assumed singularity certificate for this curve. -/
theorem pinchedStructure_not_smooth (H : _root_.AlgebraicGeometry.Scheme.SmoothFieldNormality.{u}) :
    ¬ Smooth (pinchedStructure k) := by
  intro hs
  exact pinchedGluing_not_normal k (H k (pinchedGluing k) (pinchedStructure k) hs)

/-- The pinched proper curve cannot be isomorphic to the actual projective line;
this follows unconditionally from its nonnormal affine chart. -/
theorem pinchedGluing_not_iso_projectiveP1 :
    ¬ Nonempty (pinchedGluing k ≅ Scheme.ProjectiveLine.projectiveP1 k) := by
  rintro ⟨e⟩
  exact pinchedGluing_not_normal k
    (normalStalks_of_iso (e ≪≫ (ProjectiveComparison.lineIsoP1 k).symm) (lineGluing_normal k))
end NonNormality


/-- The actual affine node scheme has the proved cubic quotient presentation. -/
def nodeCubicSchemeIso :
    Spec (.of (k[X][X] ⧸ Ideal.span ({nodeCubic k} : Set k[X][X]))) ≅ nodeScheme k :=
  Scheme.Spec.mapIso (nodeCubicEquiv k).toRingEquiv.toCommRingCatIso.symm.op
end AlgebraicGeometry.Scheme.PinchedLine

/- Migration sources: Nodal.Projective and the exact normalization comparison
from ordinary Curves.ProjectiveLine.Charts:89–241 in the frozen R5 packet
f8a3314ddecffcada2ec721d26d56a937bed9690. Native P¹ and its charts are reused.
Local normal-stalk transports retain source NormalAffine proofs. -/
