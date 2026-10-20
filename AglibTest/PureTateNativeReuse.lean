/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChangeChart
import Aglib.AlgebraicGeometry.Morphisms.Smooth.Reduced
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Exact actual-map consumers for the direct native-reuse portions of the eight-source split. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
attribute [local instance] Over.cartesianMonoidalCategory

universe u

private def nativePointedGroupIso {F : Type u} [Field F]
    (G H : Grp (FScheme F)) (hG : Curve.Properties G.X) (hH : Curve.Properties H.X)
    (e : G.X ≅ H.X) (hp : η[G.X] ≫ e.hom = η[H.X]) : G ≅ H := by
  let : IsMonHom e.hom := Curve.pointedMorphism_of_curveProperties G H hG hH e.hom hp
  exact Grp.mkIso' e

example {F : Type u} [Field F]
    (G H : Grp (FScheme F)) (hG : Curve.Properties G.X) (hH : Curve.Properties H.X)
    (e : G.X ≅ H.X) (hp : η[G.X] ≫ e.hom = η[H.X]) :
    (nativePointedGroupIso G H hG hH e hp).hom.hom.hom = e.hom := rfl

example {F : Type u} [Field F]
    (G : Grp (FScheme F)) (hG : Curve.Properties G.X) : IsCommMonObj G.X := by
  let := hG.proper
  let := hG.isGeometricallyIntegral
  exact isCommMonObj_of_isProper_of_geometricallyIntegral G.X

open WeierstrassCurve.Projective WeierstrassCurve.VariableChange

example {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    affineOver ((C • W).baseChange F) ≅ affineOver (W.baseChange F) := by
  have he : (C • W).baseChange F = (C.map (algebraMap R F)) • W.baseChange F :=
    (WeierstrassCurve.map_variableChange W C (algebraMap R F)).symm
  rw [he]
  exact affineOverIso (W.baseChange F) (C.map (algebraMap R F))

example {F : Type u} [Field F] (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) :
    (affineSpecIso W C).hom = Spec.map (CommRingCat.ofHom (affineEquiv W C).toRingHom) := rfl

example {F : Type u} [Field F] {X Y : FScheme F} (e : X ≅ Y) :
    IsOpenImmersion e.hom.left := by
  let : IsIso e.hom.left :=
    (inferInstance : IsIso ((Over.forget (Spec (.of F))).map e.hom))
  infer_instance

example {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (.of F))
    [IsFinite f] [Etale f] : IsReduced X :=
  Scheme.isReduced_of_smooth_over_field f
