/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Stalk.CodimensionOneOrder
import Aglib.AlgebraicGeometry.Stalk.DedekindCurveDimension
import Aglib.AlgebraicGeometry.Stalk.DedekindValuation
import Aglib.AlgebraicGeometry.Stalk.ResidueCharacteristic
import Aglib.AlgebraicGeometry.RationalPoint.ConstantsTriangles
import Aglib.AlgebraicGeometry.RationalPoint.ResidueUnits
import Aglib.AlgebraicGeometry.FunctionField.DedekindGenericFiberIntegral

/-!
# Native clients of actual Dedekind and rational-point stalk geometry

These examples use actual scheme stalks, residue fields, generic points and
structural arrows. The generic-fibre field square derives integrality of the
same pullback from its current native supplier. No source application wrapper
or supplied comparison map is used.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber
universe u

section Order
variable {X : Scheme.{u}}

example (hbound : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (x : CodimensionOnePoint X) : IsClosed ({x.1} : Set X) :=
  x.isClosed_singleton_of_stalk_dimension_le_one hbound

example (x y : CodimensionOnePoint X) (h : x.1 ⤳ y.1) : x = y :=
  x.eq_of_specializes y h

example [IsIntegral X] : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 :=
  X.genericPoint_stalk_dimension_zero

example (n p r : ℕ) [Fact p.Prime] (hlevel : n = p ^ r)
    (x : CodimensionOnePoint X) (haway : ringChar x.residueField ≠ p) :
    IsUnit (n : x.localRing) :=
  CodimensionOnePoint.level_isUnit_of_residueChar_ne n p r hlevel x haway

end Order

section Dedekind
variable (A F : Type u) [CommRing A] [IsDedekindDomain A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

example (y : Spec (.of A)) : ValuationRing ((Spec (.of A)).presheaf.stalk y) :=
  valuationRing_stalk_of_isDedekindDomain A y

example (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    projection A F p (horizontalLift A F p y hy) = y :=
  horizontalLift_projection A F p y hy

example (y : Y) (hy : p y = genericPoint (Spec (.of A))) :
    ∃! x : scheme A F p, projection A F p x = y :=
  existsUnique_horizontalLift A F p y hy

example (x : CodimensionOnePoint (scheme A F p)) :
    (horizontalCodimensionOneEquiv A F p).symm
      (horizontalCodimensionOneEquiv A F p x) = x :=
  (horizontalCodimensionOneEquiv A F p).symm_apply_apply x

example (x : scheme A F p) :
    (residueFieldRingEquiv A F p x).toRingHom =
      ((projection A F p).residueFieldMap x).hom :=
  residueFieldRingEquiv_toRingHom A F p x

example (x : scheme A F p) :
    (residueFieldRingEquiv A F p x).toRingHom.comp
      (horizontalResidueConstants A F p (projection A F p x)
        (projection_over_genericPoint A F p x)) = fibreResidueConstants A F p x :=
  residueFieldRingEquiv_constants A F p x

variable [IsIntegral Y] [IsDominant p]

example [IsLocallyNoetherian Y] (y : Y)
    (hdim : 1 < ringKrullDim (Y.presheaf.stalk y))
    (hy : (DedekindBase.imagePrime p y).asIdeal ≠ ⊥) :
    ∃ d : CodimensionOnePoint Y,
      p d.1 = genericPoint (Spec (.of A)) ∧ d.1 ⤳ y :=
  DedekindBase.exists_horizontal_codimensionOne_generization p y hdim hy

example [LocallyOfFiniteType p]
    (hcurve : OverField.Curve.Properties (Over.mk (pullback.snd p (baseMap A F))))
    (y : Y) : ringKrullDim (Y.presheaf.stalk y) ≤ 2 :=
  DedekindBase.stalk_dimension_le_two_of_generic_curve F p hcurve y

example (x : CodimensionOnePoint (scheme A F p))
    (a : (codimensionOneProjection A F p x).localRing) :
    letI : IsIntegral (scheme A F p) :=
      FunctionField.DedekindGenericFiber.integral_genericFiber A F p
    FunctionField.DedekindGenericFiber.functionFieldRingEquiv A F p
        ((codimensionOneProjection A F p x).toFunctionField a) =
      x.toFunctionField (stalkEquiv A F p x.1 a) := by
  let : IsIntegral (scheme A F p) :=
    FunctionField.DedekindGenericFiber.integral_genericFiber A F p
  exact functionFieldRingEquiv_toFunctionField A F p x a

end Dedekind

section RationalPoint
variable {F : Type u} [Field F] {X : Scheme.{u}} (q : RationalPoint F X)

example : q.closedMap ≫ q.localMap = q.sectionMap := q.closedTriangle

example : X.fromSpecStalk q.point ≫ q.structureMap =
    Spec.map (CommRingCat.ofHom q.constants) := q.origin_constants_triangle

example : q.residueUnitsMap (-1) = -1 := q.residueUnitsMap_neg_one

-- The retired residue-data alias is exactly the existing scheme residue equivalence.
example : IsLocalRing.ResidueField q.localRing ≃+* F := q.residueEquiv

example [CharZero F] (n : ℕ) [NeZero n] (x : CodimensionOnePoint X) :
    IsUnit (n : x.localRing) := q.level_isUnit_at n x

example [CharZero F] (n : ℕ) [NeZero n] : IsUnit (n : q.localRing) := q.level_isUnit n

variable [IsIntegral X]

example : q.genericMap ≫ q.localMap = X.fromSpecStalk (genericPoint X) := q.genericTriangle

-- The retired residue-data constants use the canonical actual stalk-to-generic map.
example : q.functionFieldConstants =
    (algebraMap q.localRing X.functionField).comp q.constants := rfl

example : q.functionFieldConstants = Scheme.functionFieldConstants X q.structureMap :=
  q.origin_fraction_constants

example [CharZero F] : CharZero X.functionField := q.functionField_charZero

example [Smooth q.structureMap] :
    (Scheme.functionFieldConstants X q.structureMap).FormallySmooth :=
  q.origin_fraction_formallySmooth

example [Smooth q.structureMap] :
    (Scheme.functionFieldConstants X q.structureMap).EssFiniteType :=
  q.origin_fraction_essFiniteType

end RationalPoint
