/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Actual Picard degree under scheme isomorphisms

The generic field map is the actual stalk map, with the generic-point equality
inserted by stalk specialization. For a scheme isomorphism it is proved
bijective, so its induced algebra is finite and has dimension one. C's actual
Picard pullback-degree theorem then proves degree invariance.

This adapter introduces no standard family. It explicitly consumes the
already reviewed universal finite-morphism norm/order family from
Picard.NormDegree, SHA256
0e7159fc9acf3656433a7a4f1786c6d76832bd7f286888bb4f33e56543e74a37,
in addition to the existing curve and product-formula inputs. It imports no
differential, Riemann–Hurwitz or Picard-representation layer.
The numerical pullback is the unchanged actual Scheme.Modules pullback and
actual C residue-weighted Picard degree.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Divisors
variable {Z W : Scheme.{u}} [IsIntegral Z] [IsIntegral W]
theorem fieldMap_bijective_of_isIso (f : Z ⟶ W) [IsIso f] :
    Function.Bijective (Scheme.functionFieldMap f) := by
  have hs {x y : W} (h : x = y) : IsIso (W.presheaf.stalkSpecializes (specializes_of_eq h)) := by
    subst y
    simpa using (inferInstance : IsIso (𝟙 (W.presheaf.stalk x)))
  haveI := hs (AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant Z f)
  exact ConcreteCategory.bijective_of_isIso
    ((W.presheaf.stalkSpecializes (specializes_of_eq
      (AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant Z f))) ≫
      f.stalkMap (genericPoint Z))

theorem fieldDegree_eq_one_of_isIso (f : Z ⟶ W) [IsIso f] :
    AlgebraicGeometry.Scheme.Hom.fieldDegree f = 1 := by
  letI := Scheme.functionFieldMapAlgebra f
  exact Module.finrank_of_bijective_algebraMap (fieldMap_bijective_of_isIso f)

theorem fieldMap_finite_of_isIso (f : Z ⟶ W) [IsIso f] :
    letI := Scheme.functionFieldMapAlgebra f
    Module.Finite W.functionField Z.functionField := by
  letI := Scheme.functionFieldMapAlgebra f
  exact Module.Finite.of_surjective (Algebra.linearMap W.functionField Z.functionField)
    (fieldMap_bijective_of_isIso f).surjective

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable {F : Type u} [Field F] {X Y : FScheme F}
include hnorm in
theorem curveDegree_pullback_iso (e : X ≅ Y) (hX : Properties X) (hY : Properties Y)
    (a : Invertible.PicardGroup Y.left) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (Invertible.pullbackClass e.hom.left a) =
      curveDegree hnormal hcomp hreg hclosed hdim hprod Y hY a := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isIntegral hnormal hcomp hY
  letI := curveProperties_isNoetherian hX
  letI := curveProperties_isNoetherian hY
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI (y : ClosedPoint Y.left) : IsDiscreteValuationRing (Y.left.presheaf.stalk y.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hY y.val y.property
  letI := hX.proper
  letI := hY.proper
  have h := Picard.NormDegree.picardDegree_pullback e.hom.left Y.hom hnorm
    (le_of_eq (curveProperties_dimension hdim hX)) (le_of_eq (curveProperties_dimension hdim hY))
    (fieldMap_finite_of_isIso e.hom.left)
    (hprod F X.left (e.hom.left ≫ Y.hom) (curveProperties_dimension hdim hX))
    (hprod F Y.left Y.hom (curveProperties_dimension hdim hY)) a
  simpa only [curveDegree, Over.w e.hom, fieldDegree_eq_one_of_isIso, Nat.cast_one, one_mul] using h
end AlgebraicGeometry.Scheme.OverField.Curve
