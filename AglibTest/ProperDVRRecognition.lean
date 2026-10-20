module

import Aglib.AlgebraicGeometry.Morphisms.Proper.DVRRecognition
import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

-- The birational input is still the actual contravariant generic-stalk map.
example {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Scheme.functionFieldMap f =
      (Y.presheaf.stalkSpecializes
        (specializes_of_eq (Scheme.map_genericPoint_of_isDominant X f)) ≫
          f.stalkMap (genericPoint X)).hom := rfl

-- The proper-birational family and all original DVR data are supplied explicitly.
example (H : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (z₀ : Y) [IsDiscreteValuationRing (Y.presheaf.stalk z₀)]
    (hdvr : ∀ z : Y, z ≠ genericPoint Y →
      IsDiscreteValuationRing (Y.presheaf.stalk z)) : IsIso f :=
  Scheme.Hom.isIso_of_dvr_off_generic H f hf z₀ hdvr

-- This exact original dimension-bound type is supplied by the stronger native theorem.
example (_hdim : Scheme.SmoothClosedPointDimension.{u})
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (hf : SmoothOfRelativeDimension 1 f) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  let := hf
  exact Scheme.smoothOfRelativeDimension_stalk_dimension_le K X f 1 x

variable (hdesc : Scheme.RegularityDescent.FlatLocalRegularityDescent.{u})
  (hreg : Scheme.SmoothFieldRegularity.{u}) (hdim : Scheme.SmoothClosedPointDimension.{u})
  (K : Type u) [Field K] {X Y : Scheme.{u}}

-- No source integrality, closed chart point or target dimension bound is added.
example [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [Etale j] (f : X ⟶ Spec (.of K))
    (hf : SmoothOfRelativeDimension 1 f) (x : X)
    (himage : j x ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j x)) :=
  Scheme.dvr_at_image_of_etale_smooth_curve_chart_any_point hdesc hreg hdim K j f hf x himage

example [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [Etale j] (b : X ⟶ Spec (.of (Polynomial K))) [Etale b]
    (x : X) (himage : j x ≠ genericPoint Y) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j x)) :=
  Scheme.dvr_at_image_of_etale_affine_line_chart hdesc hreg hdim K j b x himage

-- The open-chart endpoint transports along the original stalkMap, with closed image.
example [IsIntegral Y] (j : X ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 (j ≫ p)]
    (q : X) (hq : IsClosed ({j q} : Set Y)) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j q)) :=
  Scheme.smoothChart_closedPoint_dvr j p hreg hdim q hq
