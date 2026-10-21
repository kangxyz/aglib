/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ExtensionPoints
public import Aglib.AlgebraicGeometry.Curves.Basic

/-!
# The separate coordinate-operation compatibility inputs

Source: ordinary R5 Weierstrass.Points, lines 233–274 and 533–587.
The set bijection is proved in ExtensionPoints. GroupCompatibility supplies
the exact chord/tangent comparison with every actual pointed group law.
The extension version evaluates the original k-group on Spec K; the retained
bundlers accept the proved comparison as their explicit argument.
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

/-- Classical equality on the field of coordinate points. The field guard keeps this local
instance within the original field-valued group-comparison interface. -/
@[nolint unusedArguments]
local instance fieldDecidableEq (F : Type u) [Field F] : DecidableEq F := Classical.decEq F

variable {k K : Type u} [Field k] [Field K]

/-- Retained source-corollary algebraic comparison, independent of every Tate parameter.
Milne EC2 I.Prop4.10/Rem4.11 pp.32–33 compare chord/tangent operations with the
regular divisor-class law; AV I.Cor1.2/Rem1.3 p.9 imply uniqueness with fixed origin.
Characteristic zero ensures the perfect-field scope. The explicit implementation bridge
matches mathlib's actual formulas and these actual Proj chart points to that classical
law. GroupCompatibility proves this retained family through the actual
point-ideal, class-group and Abel-class maps; this is a source-corollary
interface rather than a verbatim source statement. The supplied group law
is a genuine group object on this same literal cubic. -/
def CoordinatePointGroupCompatibility : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (W : WeierstrassCurve k), W.Δ ≠ 0 →
    ∀ (L : PointedGroupLaw (curveOver W) (originOver W)),
    let : GrpObj (curveOver W) := L.law
    ∀ P Q : W.toAffine.Point,
      coordinatePoint W (P + Q) = coordinatePoint W P * coordinatePoint W Q

/-- Bundling uses the separate comparison for the actual constructed coordinate map. -/
def coordinateGroupHom [CharZero k] (hcomp : CoordinatePointGroupCompatibility.{u})
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    Multiplicative W.toAffine.Point →* (𝟙_ (FScheme k) ⟶ curveOver W) := by
  let : GrpObj (curveOver W) := L.law
  exact { toFun := fun P => coordinatePoint W P.toAdd
          map_one' := L.origin.symm
          map_mul' := fun P Q => hcomp k W hΔ L P.toAdd Q.toAdd }

/-- Coordinate bijectivity is proved from the literal chart; only operation compatibility
is retained separately. -/
def coordinateGroupEquiv [CharZero k] [IsAlgClosed k]
    (hcomp : CoordinatePointGroupCompatibility.{u}) (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    Multiplicative W.toAffine.Point ≃* (𝟙_ (FScheme k) ⟶ curveOver W) := by
  let : GrpObj (curveOver W) := L.law
  exact MulEquiv.ofBijective (coordinateGroupHom hcomp W hΔ L)
    ⟨coordinatePoint_injective W, coordinatePoint_surjective W hΔ⟩


/-- Universal scalar-extension version of the independent chord/tangent versus
pointed algebraic group-law comparison. The group operation is that of the original
k-group evaluated on Spec K. No group chosen over K, Tate parameter, power map,
algebraization, or degree is an input to this compatibility family.

Source-corollary boundary: Milne EC2 I.Prop4.10/Rem4.11 pp.32–33 identify
chord/tangent with the regular divisor-class law; AV I.Cor1.2/Rem1.3 p.9
give uniqueness for the chosen origin. Here the same comparison is interpreted
naturally under scalar extension and on the original scheme’s point functor.
GroupCompatibility proves the match to these exact Lean formulas, including
the original group's point functor and actual scalar-extension comparisons.
The interface is a source corollary rather than a verbatim source statement. -/
def CoordinatePointExtensionGroupCompatibility : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] (f : k →+* K)
    (W : WeierstrassCurve k), W.Δ ≠ 0 →
    ∀ (L : PointedGroupLaw (curveOver W) (originOver W)),
    let : GrpObj (curveOver W) := L.law
    ∀ P Q : (W.map f).toAffine.Point,
      coordinatePointExtension W f (P + Q) =
        coordinatePointExtension W f P * coordinatePointExtension W f Q

/-- Coordinate evaluation as a homomorphism to the original curve's extension-valued points,
conditional on the supplied operation-compatibility theorem and pointed group law. -/
def coordinateExtensionGroupHom [CharZero k]
    (hcomp : CoordinatePointExtensionGroupCompatibility.{u})
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    Multiplicative (W.map f).toAffine.Point →* (extensionPointSource f ⟶ curveOver W) := by
  let : GrpObj (curveOver W) := L.law
  exact { toFun := fun P => coordinatePointExtension W f P.toAdd
          map_one' := by
            change originOverExtension W f = toUnit _ ≫ η[(curveOver W)]
            rw [L.origin]
            apply Over.OverMorphism.ext
            rfl
          map_mul' := fun P Q => hcomp k K f W hΔ L P.toAdd Q.toAdd }

/-- Group equivalence for the original group's K-valued points; bijectivity is
proved by coordinate evaluation, and only the universal operation comparison is retained. -/
def coordinateExtensionGroupEquiv [CharZero k]
    (hcomp : CoordinatePointExtensionGroupCompatibility.{u})
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0)
    (L : PointedGroupLaw (curveOver W) (originOver W)) :
    let : GrpObj (curveOver W) := L.law
    Multiplicative (W.map f).toAffine.Point ≃* (extensionPointSource f ⟶ curveOver W) := by
  let : GrpObj (curveOver W) := L.law
  exact MulEquiv.ofBijective (coordinateExtensionGroupHom hcomp W f hΔ L)
    ⟨coordinatePointExtension_injective W f, coordinatePointExtension_surjective W f hΔ⟩


end WeierstrassCurve.Projective
