/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Parameters
public import Aglib.AlgebraicGeometry.Curves.Picard.TorsionSections.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Semicontinuity
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-! # The actual closed reduced power-nonvanishing parameter locus

Apply native proper semicontinuity to the actual tensor power of the bounded
graph family, with finite presentation and relative flatness supplied by its
actual line-bundle structure. Its H0-nonvanishing locus has the native reduced
closed subscheme structure. The literal ordinary point-fibre dimension agrees
with the actual graph-family specialization over the point's residue field.
Degree zero and proper geometrically integral constants make every nonzero H0
on that locus exactly one-dimensional, over arbitrary residue fields.

This file does not assert local power trivializations, Picard torsion finiteness,
Picard representability or proper base change for etale cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S Y : Scheme.{u}} (p : Y ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsProper p]
  (o : S ⟶ Y) (ho : o ≫ p = 𝟙 S)

/-- The actual tensor power of the bounded graph family. -/
def powerLineBundle (g n : ℕ) : LineBundle (pullback p (parameter p g).hom) :=
  tensorPowerLineBundle _ (lineBundle p o ho g) n

/-- Original point-fibre H0 dimension of the actual tensor-power coefficient. -/
def powerH0Dimension (g n : ℕ) (y : (parameter p g).left) : ℕ :=
  modulePointFiberCohomologyDimension (pullback.snd p (parameter p g).hom)
    (powerLineBundle p o ho g n).val 0 y

/-- Coherence is supplied by the actual line bundle's finite presentation. -/
theorem powerLineBundle_affineLocallyFiniteType (g n : ℕ) :
    affineLocallyFiniteType _ (powerLineBundle p o ho g n).val := by
  let := lineBundle_isFinitePresentation _ (powerLineBundle p o ho g n)
  exact affineLocallyFiniteType_of_finitePresentation _

/-- Smoothness of the original curve family supplies coefficient relative
flatness for every actual tensor power. -/
theorem powerLineBundle_relativeFlat (g n : ℕ) :
    Modules.relativeFlat (pullback.snd p (parameter p g).hom)
      (powerLineBundle p o ho g n).val := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  exact relativeFlat_of_flat _ (powerLineBundle p o ho g n)

/-- The actual ordinary point-fibre H0 dimension agrees with the H0 of the
original graph-family pullback at the same residue-field point. -/
theorem powerH0Dimension_eq_fibre (g n : ℕ) (y : (parameter p g).left) :
    powerH0Dimension p o ho g n y =
      Module.finrank ((parameter p g).left.residueField y)
        (moduleCohomology _
          (Over.mk (pullback.snd p
            ((parameter p g).left.fromSpecResidueField y ≫ (parameter p g).hom)))
          (pullbackLineBundle (Hom.familyMap p (parameter p g).hom
            ((parameter p g).left.fromSpecResidueField y ≫ (parameter p g).hom)
            ((parameter p g).left.fromSpecResidueField y) rfl)
            (powerLineBundle p o ho g n)).val 0) := by
  let t := (parameter p g).hom
  let a := (parameter p g).left.fromSpecResidueField y
  let f := pullback.snd p t
  let M : (pullback p t).Modules := (powerLineBundle p o ho g n).val
  let h := Hom.familyMap_isPullback p t (a ≫ t) a rfl
  let e := h.isoPullback
  let C : (Modules.pullback e.hom).obj ((Modules.pullback (pullback.fst f a)).obj M) ≅
      (Modules.pullback (Hom.familyMap p t (a ≫ t) a rfl)).obj M :=
    (Modules.pullbackComp e.hom (pullback.fst f a)).app M ≪≫
      (Modules.pullbackCongr h.isoPullback_hom_fst).app M
  exact finrank_moduleCohomology_eq_of_isIso e.hom (pullback.snd f a)
    (pullback.snd p (a ≫ t)) h.isoPullback_hom_snd
    ((Modules.pullback (pullback.fst f a)).obj M) C 0

/-- Every original field specialization of the actual tensor power has degree
zero, by the accepted degree-zero graph family and the original Picard maps. -/
theorem powerLineBundle_degree_at_field_point
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {g : ℕ}
    (a : Spec (.of k) ⟶ (parameter p g).left)
    (ha : a ≫ (parameter p g).hom = t)
    (hY : Properties (Over.mk (pullback.snd p t))) (n : ℕ) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY
      (classOf _ (pullbackLineBundle (Hom.familyMap p (parameter p g).hom t a ha)
        (powerLineBundle p o ho g n))) = 0 := by
  change curveDegree _ _ _ _ _ _ _ _
    ((PullbackTensor.Local.pullbackHom _) (classOf _ (powerLineBundle p o ho g n))) = 0
  rw [powerLineBundle, classOf_tensorPower, map_nsmul, map_nsmul,
    PullbackTensor.Local.pullbackHom_apply,
    lineBundle_degree_at_field_point p o ho t a ha hY, nsmul_zero]

section ClosedLocus

variable [IsNoetherian S]

/-- Native proper semicontinuity for the original H0 dimensions of the actual
bounded graph tensor power. -/
theorem upperSemicontinuous_powerH0Dimension (g n : ℕ) :
    UpperSemicontinuous (powerH0Dimension p o ho g n) := by
  let : IsNoetherian (parameter p g).left := parameter_isNoetherian p g
  exact upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper
    (pullback.snd p (parameter p g).hom) (powerLineBundle p o ho g n).val
    (powerLineBundle_affineLocallyFiniteType p o ho g n)
    (powerLineBundle_relativeFlat p o ho g n) 0

/-- The closed support is defined by actual H0 dimension at least one, not by
an assumed torsion certificate or a set of abstract Picard classes. -/
def powerNonvanishingSupport (g n : ℕ) : Closeds (parameter p g).left :=
  ⟨(powerH0Dimension p o ho g n) ⁻¹' Set.Ici 1,
    (upperSemicontinuous_powerH0Dimension p o ho g n).isClosed_preimage 1⟩

@[simp]
theorem mem_powerNonvanishingSupport (g n : ℕ) (y : (parameter p g).left) :
    y ∈ powerNonvanishingSupport p o ho g n ↔ 0 < powerH0Dimension p o ho g n y := by
  change 1 ≤ powerH0Dimension p o ho g n y ↔ 0 < powerH0Dimension p o ho g n y
  omega

/-- The native vanishing ideal gives the reduced closed scheme structure. -/
def powerNonvanishingIdeal (g n : ℕ) : (parameter p g).left.IdealSheafData :=
  IdealSheafData.vanishingIdeal (powerNonvanishingSupport p o ho g n)

/-- The actual reduced closed parameter scheme. -/
def powerNonvanishingLocus (g n : ℕ) : Scheme.{u} :=
  (powerNonvanishingIdeal p o ho g n).subscheme

/-- Its actual closed immersion into the bounded ordered parameter scheme. -/
def powerNonvanishingι (g n : ℕ) :
    powerNonvanishingLocus p o ho g n ⟶ (parameter p g).left :=
  (powerNonvanishingIdeal p o ho g n).subschemeι

instance powerNonvanishingι_isClosedImmersion (g n : ℕ) :
    IsClosedImmersion (powerNonvanishingι p o ho g n) := by
  dsimp only [powerNonvanishingι]
  infer_instance

instance powerNonvanishingLocus_isReduced (g n : ℕ) :
    IsReduced (powerNonvanishingLocus p o ho g n) := by
  apply IdealSheafData.subscheme_reduced_of_radical
  apply IdealSheafData.ext
  funext V
  simp only [IdealSheafData.radical_ideal, powerNonvanishingIdeal,
    IdealSheafData.vanishingIdeal_ideal]
  exact Ideal.radical_eq_iff.mpr (PrimeSpectrum.isRadical_vanishingIdeal _)

instance powerNonvanishingLocus_isNoetherian (g n : ℕ) :
    IsNoetherian (powerNonvanishingLocus p o ho g n) := by
  let : IsNoetherian (parameter p g).left := parameter_isNoetherian p g
  let : IsLocallyNoetherian (powerNonvanishingLocus p o ho g n) :=
    LocallyOfFiniteType.isLocallyNoetherian (powerNonvanishingι p o ho g n)
  let : CompactSpace (powerNonvanishingLocus p o ho g n) :=
    QuasiCompact.compactSpace_of_compactSpace (powerNonvanishingι p o ho g n)
  exact ⟨⟩

instance powerNonvanishingLocus_isProper (g n : ℕ) :
    IsProper (powerNonvanishingι p o ho g n ≫ (parameter p g).hom) := inferInstance

/-- The native closed immersion has exactly the H0-nonvanishing support. -/
theorem range_powerNonvanishingι (g n : ℕ) :
    Set.range (powerNonvanishingι p o ho g n) = powerNonvanishingSupport p o ho g n := by
  exact (IdealSheafData.range_subschemeι (powerNonvanishingIdeal p o ho g n)).trans
    (IdealSheafData.coe_support_vanishingIdeal _)

/-- Every point of the reduced closed locus lies on the original nonvanishing
support before any change of fibre is performed. -/
theorem powerH0Dimension_pos_on_locus (g n : ℕ)
    (z : powerNonvanishingLocus p o ho g n) :
    0 < powerH0Dimension p o ho g n (powerNonvanishingι p o ho g n z) := by
  apply (mem_powerNonvanishingSupport p o ho g n _).mp
  change powerNonvanishingι p o ho g n z ∈
    (powerNonvanishingSupport p o ho g n : Set (parameter p g).left)
  rw [← range_powerNonvanishingι p o ho g n]
  exact Set.mem_range_self z

end ClosedLocus

section FieldCurve

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

include hX

/-- The actual original point-fibre H0 dimension is exactly one wherever it
is nonzero. All residue fields, including nonclosed points, are retained. -/
theorem powerH0Dimension_eq_one_of_pos (g n : ℕ) (y : (parameter X.hom g).left)
    (hy : 0 < powerH0Dimension X.hom o ho g n y) :
    powerH0Dimension X.hom o ho g n y = 1 := by
  let t := (parameter X.hom g).left.fromSpecResidueField y ≫ (parameter X.hom g).hom
  let a := (parameter X.hom g).left.fromSpecResidueField y
  let Z : FScheme ((parameter X.hom g).left.residueField y) := Over.mk (pullback.snd X.hom t)
  have hZ : Properties Z := curveProperties_baseChange hX _ t
  let : IsIntegral Z.left := PointDivisor.isIntegral_of_properties Z hZ
  let : IsNoetherian Z.left := curveProperties_isNoetherian hZ
  let (x : ClosedPoint Z.left) := PointDivisor.isDiscreteValuationRing_stalk Z hZ x
  let : IsProper Z.hom := hZ.proper
  let : GeometricallyIntegral Z.hom :=
    curveProperties_geometricallyIntegral smoothFieldNormality normalComponentsOpen hZ
  let L := pullbackLineBundle (Hom.familyMap X.hom (parameter X.hom g).hom t a rfl)
    (powerLineBundle X.hom o ho g n)
  have hd := powerLineBundle_degree_at_field_point X.hom o ho t a rfl hZ n
  have hdim := curveProperties_dimension smoothFieldDimension hZ
  have hdegree : Picard.Degree.lineBundleDegree Z.left Z.hom hdim.le
      (Picard.Degree.properCurveProductFormula _ Z.left Z.hom hdim) L = 0 := hd
  rw [powerH0Dimension_eq_fibre] at hy ⊢
  exact Picard.TorsionSections.lineBundle_h0_finrank_eq_one_of_pos_of_proper
    Z hdim L hdegree hy

/-- The original dimension function, restricted to its actual reduced closed
support, is the constant function one. -/
theorem powerH0Dimension_eq_one_on_locus (g n : ℕ)
    (z : powerNonvanishingLocus X.hom o ho g n) :
    powerH0Dimension X.hom o ho g n (powerNonvanishingι X.hom o ho g n z) = 1 :=
  powerH0Dimension_eq_one_of_pos X hX o ho g n _
    (powerH0Dimension_pos_on_locus X.hom o ho g n z)

end FieldCurve

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
