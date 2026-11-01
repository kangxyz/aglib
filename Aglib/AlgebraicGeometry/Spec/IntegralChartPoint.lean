/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The specified closed point of an actual integral local chart

Integrality makes every point above the closed base point maximal. Locality
then identifies that point with the unique original closed point. The whole
chart structural equation therefore retains the specified original point;
no residue-field identification is needed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- An integral local affine chart sends its original closed point to any
specified point lying over the original closed base point. -/
theorem integralLocalChart_closedPoint
    (R B : Type u) [CommRing R] [IsLocalRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.IsIntegral R B]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of R)) (c : Spec (.of B) ≅ Z)
    (hc : c.hom ≫ p = Spec.algebraMap R B)
    (x : Z) (hx : p x = IsLocalRing.closedPoint R) :
    c.hom (IsLocalRing.closedPoint B) = x := by
  have hci : c.inv ≫ Spec.algebraMap R B = p := by
    rw [← hc, Iso.inv_hom_id_assoc]
  have hbase : Spec.algebraMap R B (c.inv x) = IsLocalRing.closedPoint R :=
    (congrArg (fun q : Z ⟶ Spec (.of R) => q x) hci).trans hx
  let : (c.inv x).asIdeal.IsPrime := (c.inv x).2
  have hm : (c.inv x).asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _ (by
      change (Spec.algebraMap R B (c.inv x)).asIdeal.IsMaximal
      rw [hbase]
      exact IsLocalRing.maximalIdeal.isMaximal R)
  have hp : c.inv x = IsLocalRing.closedPoint B :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
  rw [← hp]
  exact Scheme.inv_hom_apply c x

end AlgebraicGeometry.Scheme
