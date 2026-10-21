/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne

/-!
# Actual local spectra and rational-section triangles

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSection`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `eb2e49d19b97fba8abdedcfb7966f3c83a2b22d4ade66d40e1398f9ac94f8213`, selected lines [[15,
58]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RationalPoint
variable {F : Type u} [Field F] {X : Scheme.{u}} (q : RationalPoint F X)

include q in
/-- Every nonzero natural level is a unit at each indexed stalk over a characteristic-zero field.
-/
theorem level_isUnit_at [CharZero F] (n : ℕ) [NeZero n]
    (x : CodimensionOnePoint X) : IsUnit (n : x.localRing) := by
  have hn : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [map_natCast] using hn.map (q.constantsAt x.1)

/-- The spectrum of the actual rational-point stalk. -/
abbrev localScheme : Scheme.{u} := Spec q.localRing

/-- The canonical local-spectrum morphism at the actual rational point. -/
def localMap : q.localScheme ⟶ X := X.fromSpecStalk q.point

/-- The field-valued map induced by section evaluation on the actual stalk. -/
def closedMap : Spec (.of F) ⟶ q.localScheme :=
  Spec.map (CommRingCat.ofHom q.evaluation)

/-- The local closed-field map recovers the given rational section. -/
theorem closedTriangle : q.closedMap ≫ q.localMap = q.sectionMap :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk q.sectionMap

variable [IsIntegral X]

/-- The actual fraction map gives a map from the generic-field spectrum to the local spectrum. -/
def genericMap : Spec X.functionField ⟶ q.localScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap q.localRing X.functionField))

/-- The local generic map recovers the actual generic-point morphism of the scheme. -/
theorem genericTriangle :
    q.genericMap ≫ q.localMap = X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes q.point)

end AlgebraicGeometry.Scheme.RationalPoint
