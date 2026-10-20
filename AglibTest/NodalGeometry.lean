/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.CriticalPoint
public import Aglib.AlgebraicGeometry.Curves.Nodal.SplitChart
public import Aglib.AlgebraicGeometry.Curves.Nodal.CoordinateTransport
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.ProjectivePinching
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.TwoPoints

/-! Tests of the original normalization maps, scalar triangles, and actual section endpoints. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped Polynomial

universe u

namespace NodalGeometryTest

variable (k : Type u) [Field k]

example :
    Nat.card {z : Scheme.PinchedLine.lineGluing k //
      Scheme.PinchedLine.gluedNormalizationMap k z = Scheme.PinchedLine.gluedNodePoint k} = 2 :=
  Scheme.PinchedLine.glued_normalization_fibre_card k

example :
    IsProper (Scheme.PinchedLine.pinchedStructure k) := inferInstance

example :
    ¬ Nonempty (Scheme.PinchedLine.pinchedGluing k ≅ Scheme.ProjectiveLine.projectiveP1 k) :=
  Scheme.PinchedLine.pinchedGluing_not_iso_projectiveP1 k

example (s t : Spec (.of k) ⟶ Scheme.ProjectiveLine.projectiveP1 k)
    (hs : s ≫ Scheme.ProjectiveLine.structureMap k = 𝟙 _)
    (ht : t ≫ Scheme.ProjectiveLine.structureMap k = 𝟙 _) (hne : s ≠ t) :
    s ≫ (Scheme.ProjectiveLine.TwoPoints.normalizePair k s t hs ht hne).hom.left =
      Spec.map (CommRingCat.ofHom (evalRingHom (0 : k))) ≫ Scheme.ProjectiveLine.chart k 0 :=
  Scheme.ProjectiveLine.TwoPoints.normalizePair_first k s t hs ht hne

example (a b r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (WeierstrassCurve.CriticalCubic.coordinateNodeEquiv k a b r s hrs hr hs
      (WeierstrassCurve.affineX (WeierstrassCurve.CriticalCubic.equation k a b)) : k[X]) =
      C ((s - r) ^ 2) * (Polynomial.PinchedPair.conductor k : k[X]) := by
  rw [WeierstrassCurve.CriticalCubic.coordinateNodeEquiv_X]
  rfl

example (a b r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    WeierstrassCurve.CriticalCubic.ProjectivePinching.projectiveNormalization k a b r s hrs hr hs ≫
      WeierstrassCurve.Projective.structureMap
        (WeierstrassCurve.CriticalCubic.equation k a b) = Scheme.ProjectiveLine.structureMap k :=
  WeierstrassCurve.CriticalCubic.ProjectivePinching.projectiveNormalization_over k a b r s hrs hr hs

example {R : Type u} [CommRing R] [HenselianLocalRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ ∈ IsLocalRing.maximalIdeal R)
    (h4 : W.a₄ ∈ IsLocalRing.maximalIdeal R) (hb : IsUnit W.b₂) :
    ∃ r t : R, r ∈ IsLocalRing.maximalIdeal R ∧ t ∈ IsLocalRing.maximalIdeal R ∧
      W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄) = 0 ∧
      2 * t + W.a₁ * r + W.a₃ = 0 :=
  WeierstrassCurve.CriticalPoint.exists_critical_origin W h3 h4 hb

end NodalGeometryTest
