/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.OpenRestriction
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.RingTheory.DiscreteValuationRing.OrderTransport.FieldMap

/-! # Original principal divisors under open restriction

The actual open-immersion stalk isomorphism and its compatible map between
actual function fields preserve local order. Pointwise application identifies
the restriction of the original principal divisor with the principal divisor
of the original rational-function pullback. Integral schemes provide the
nonempty source needed for dominance; the Jacobson hypothesis is used only
for the existing closed-point divisor restriction.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors

variable {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
  [IsNoetherian U] [IsNoetherian X]
  (j : U ⟶ X) [IsOpenImmersion j]

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j

/-- The original function-field pullback preserves the original local order
at points where the two actual stalks are DVRs, including the zero function. -/
theorem order_functionFieldMap_openImmersion (x : U)
    [IsDiscreteValuationRing (U.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk (j x))]
    (f : X.functionField) :
    U.ord (Scheme.functionFieldMap j f) x = X.ord f (j x) := by
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have he : (Scheme.functionFieldMap j).comp
      (algebraMap (X.presheaf.stalk (j x)) X.functionField) =
      (algebraMap (U.presheaf.stalk x) U.functionField).comp e.toRingHom := by
    ext a
    exact Scheme.functionFieldMap_stalk j x a
  have h := Ring.ordFrac_map_eq_of_ringEquiv e (Scheme.functionFieldMap j) he f
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one (coheight_eq_one_of_dvr U x),
    Scheme.ord_eq_ordHom_of_coheight_eq_one (coheight_eq_one_of_dvr X (j x))]
  exact congrArg (fun v : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (v.unzeroD 1)) h

/-- Restriction of the original principal divisor is the principal divisor of
the original pullback on actual function-field units. No finite-morphism
hypothesis or replacement divisor model is used. -/
theorem openRestriction_principal [JacobsonSpace X]
    [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (f : X.functionFieldˣ) :
    openRestriction j (principal X (Additive.ofMul f)) =
      principal U (Additive.ofMul (Scheme.functionFieldUnitMap j f)) := by
  ext x
  let : IsDiscreteValuationRing (X.presheaf.stalk (j x.val)) :=
    inferInstanceAs (IsDiscreteValuationRing
      (X.presheaf.stalk (ClosedPoint.openEmbedding j x).val))
  exact (order_functionFieldMap_openImmersion j x.val (f : X.functionField)).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Divisors
