/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Descent.FlatLocal
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# DVR stalks from actual étale smooth-curve charts

The actual étale stalk map supplies the native equality of dimensions. The existing
flat-local regularity-descent family remains an explicit input. The original smooth
regularity and closed-point dimension inputs remain in the public chart interfaces;
the native all-stalk dimension bound supplies the stronger dimension step internally.

Selected source: `R5Lab/Aglib/AlgebraicGeometry/Stalk/EtaleCurveDVR.lean`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9293a7e3552b7c0871413e8a67b4cc51675d0207806a6b0a31d984fef883f894`.
The two general pure-ring helper declarations are outside this selected scheme-consumer cut.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- At a nongeneric point of an integral scheme, the actual stalk is not a field. -/
lemma not_isField_stalk_of_ne_genericPoint
    (Y : Scheme.{u}) [IsIntegral Y] (y : Y) (hy : y ≠ genericPoint Y) :
    ¬ IsField (Y.presheaf.stalk y) := by
  intro hfield
  have hz : Order.coheight y = 0 := by
    have hdim := ringKrullDim_eq_zero_of_isField hfield
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  have hmax := Order.coheight_eq_zero.mp hz
  have hback : y ⤳ genericPoint Y := hmax (genericPoint_specializes y)
  exact hy (hback.antisymm (genericPoint_specializes y)).eq

/-- Every nongeneric image of an actual étale smooth-curve chart has a DVR stalk.
The source need not be integral, and the chart point need not be closed. -/
lemma dvr_at_image_of_etale_smooth_curve_chart_any_point
    (hdesc : RegularityDescent.FlatLocalRegularityDescent.{u})
    (hreg : SmoothFieldRegularity.{u}) (_hdim : SmoothClosedPointDimension.{u})
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [Etale j] (f : X ⟶ Spec (.of K))
    (hf : SmoothOfRelativeDimension 1 f) (x : X)
    (himage : j x ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j x)) := by
  let : SmoothOfRelativeDimension 1 f := hf
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hregular := RegularityDescent.regular_at_image hdesc j x
    (hreg K X f inferInstance x)
  have hbound : ringKrullDim (Y.presheaf.stalk (j x)) ≤ 1 := by
    rw [← ringKrullDim_stalk_eq_of_etale j x]
    exact smoothOfRelativeDimension_stalk_dimension_le K X f 1 x
  have hnotfield := not_isField_stalk_of_ne_genericPoint Y (j x) himage
  have hnzero : ¬ ringKrullDim (Y.presheaf.stalk (j x)) ≤ 0 := by
    intro hz
    let : Ring.KrullDimLE 0 (Y.presheaf.stalk (j x)) := Ring.krullDimLE_iff.mpr hz
    exact hnotfield Ring.KrullDimLE.isField_of_isDomain
  have hdim : ringKrullDim (Y.presheaf.stalk (j x)) = 1 :=
    le_antisymm hbound (Order.succ_le_of_lt (lt_of_not_ge hnzero))
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hc := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (Y.presheaf.stalk (j x))).mp hregular
  rw [hdim] at hc
  exact_mod_cast hc

/-- The original closed-point chart interface follows from the arbitrary-point theorem.
The closed-point and smooth-family premises are retained exactly. -/
lemma dvr_at_image_of_etale_smooth_curve_chart
    (hdesc : RegularityDescent.FlatLocalRegularityDescent.{u})
    (hreg : SmoothFieldRegularity.{u}) (hdim : SmoothClosedPointDimension.{u})
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [Etale j] (f : X ⟶ Spec (.of K))
    (hf : SmoothOfRelativeDimension 1 f) (x : X)
    (_hx : IsClosed ({x} : Set X)) (himage : j x ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j x)) :=
  dvr_at_image_of_etale_smooth_curve_chart_any_point hdesc hreg hdim K j f hf x himage

/-- An actual étale affine-line chart supplies the smooth curve structure. Its
structural morphism is the literal Spec map of the polynomial algebra map. -/
lemma dvr_at_image_of_etale_affine_line_chart
    (hdesc : RegularityDescent.FlatLocalRegularityDescent.{u})
    (hreg : SmoothFieldRegularity.{u}) (hdim : SmoothClosedPointDimension.{u})
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [Etale j] (b : X ⟶ Spec (.of (Polynomial K))) [Etale b]
    (x : X) (himage : j x ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j x)) := by
  let p : Spec (.of (Polynomial K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))
  have : SmoothOfRelativeDimension 1 p := by
    dsimp only [p]
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    change (algebraMap K (Polynomial K)).IsStandardSmoothOfRelativeDimension 1
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 K (MvPolynomial PUnit.{u+1} K) := by
      simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial K PUnit.{u+1}
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv K PUnit.{u+1})
  have : SmoothOfRelativeDimension 1 (b ≫ p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  exact dvr_at_image_of_etale_smooth_curve_chart_any_point hdesc hreg hdim K j
    (b ≫ p) inferInstance x himage

end AlgebraicGeometry.Scheme
