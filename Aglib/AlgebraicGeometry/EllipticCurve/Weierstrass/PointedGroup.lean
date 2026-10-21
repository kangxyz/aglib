/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.GeometryInputs
public import Aglib.AlgebraicGeometry.Curves.GenusOneGroupLaw

/-!
# Conditional genus-one group construction on the literal cubic

Source: ordinary R5 Weierstrass.Projective, lines 382–419.
This adapter retains every native genus-one prerequisite, including
Picard representability and the explicit exact Weierstrass geometry argument.
The latter has a proved supplier in Geometry; representability remains an
external prerequisite of this group-law construction.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
namespace WeierstrassCurve.Projective
universe u
attribute [local instance] Over.cartesianMonoidalCategory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
variable {k : Type u} [Field k]

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : Abel.FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hgenus : ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
variable (hrep : DegreeZeroPicardRepresentability hnormal hcomp hreg hclosed hdim hprod htensor)
variable (hweierstrass : NonsingularWeierstrassGeometry.{u})
variable (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)

/-- A group law on this literal nonsingular cubic, with exactly its constructed infinity section.
The existing native genus-one prerequisite families and the separate
geometry-only Weierstrass family are explicit arguments. -/
def pointedGroupLaw : PointedGroupLaw (curveOver W) (originOver W) :=
  genusOnePointedGroupLaw hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase
    hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep
    (curveOver W) (hweierstrass k W hΔ).1 (hweierstrass k W hΔ).2 (originOver W)

local notation "L" => pointedGroupLaw hnormal hcomp hreg hclosed hdim hprod htensor hcartier
  hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep
  hweierstrass W hΔ

/-- The actual pointed proper Weierstrass group scheme on the literal Proj cubic. -/
def groupScheme : Grp (FScheme k) where
  X := curveOver W
  grp := (L).law

local notation "G" => groupScheme hnormal hcomp hreg hclosed hdim hprod htensor hcartier
  hbase hdivisor hnorm hgenus hrr hvanish hhigher hregular hlocal hrep
  hweierstrass W hΔ

@[simp] theorem groupScheme_origin : (η[(G).X]).left = infinitySection W := by
  exact congrArg (fun f : 𝟙_ (FScheme k) ⟶ curveOver W => f.left) (L).origin

theorem groupScheme_curve : Properties (G).X := (hweierstrass k W hΔ).1

theorem groupScheme_genus : coherentGenus k (G).X = 1 := (hweierstrass k W hΔ).2


end WeierstrassCurve.Projective
