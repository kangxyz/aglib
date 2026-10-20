/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Mathlib.Algebra.CharP.Algebra

/-!
# Completion of the actual local ring of a rational point

The ring and field are constructed from the actual stalk. The residue map
uses the rational section, and the field embedding extends the actual generic
stalk localization. This module imports no K-theory or cohomology.
-/

@[expose] public section




noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.RationalPoint.Completion
universe u
variable {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
  (q : RationalPoint F X) [IsDiscreteValuationRing q.localRing]

/-- Completion of the actual structure-sheaf stalk at the rational point. -/
abbrev Ring := AdicCompletion (maximalIdeal q.localRing) q.localRing

/-- Fraction field of the completed actual stalk. -/
abbrev FractionField := FractionRing (Ring q)

/-- The canonical ring map from the local ring at the rational point to its adic completion. -/
abbrev completionMap : q.localRing →+* Ring q := algebraMap q.localRing (Ring q)

/-- Canonical residue equivalence obtained from the original rational section. -/
def residueEquiv : ResidueField (Ring q) ≃+* F :=
  AdicCompletion.residueFieldEquivOfEquiv q.localRing q.residueEquiv

theorem residue_triangle :
    (residueEquiv q).toRingHom.comp (ResidueField.map (completionMap q)) =
      q.residueEquiv.toRingHom :=
  AdicCompletion.residueFieldEquivOfEquiv_comp q.localRing q.residueEquiv

/-- Scalar structure from the actual generic stalk into the completed fraction field. -/
@[instance_reducible] def fractionAlgebra : Algebra X.functionField (FractionField q) :=
  (AdicCompletion.fractionRingMap q.localRing X.functionField).toAlgebra

/-- Scalar structure through actual origin-stalk constants. -/
@[instance_reducible] def constantsAlgebra : Algebra F (FractionField q) :=
  (AdicCompletion.fractionRingConstantsMap q.localRing q.constants).toAlgebra

/-- The function-field algebra structure on the fraction field of the completed local ring,
induced by the generic-stalk map. -/
local instance : Algebra X.functionField (FractionField q) := fractionAlgebra q
/-- The base-field algebra structure on the fraction field of the completed local ring, induced
through constants in the original stalk. -/
local instance : Algebra F (FractionField q) := constantsAlgebra q

/-- The actual function-field map extends the original stalk map. -/
theorem fraction_triangle (r : q.localRing) :
    algebraMap X.functionField (FractionField q) (algebraMap q.localRing X.functionField r) =
      algebraMap (Ring q) (FractionField q) (completionMap q r) :=
  AdicCompletion.fractionRingMap_algebraMap q.localRing X.functionField r

/-- Constants through the fraction-field embedding agree with constants through the stalk. -/
theorem constants_triangle :
    algebraMap F (FractionField q) =
      (algebraMap X.functionField (FractionField q)).comp q.functionFieldConstants :=
  AdicCompletion.fractionRingConstantsMap_eq_comp q.localRing q.constants X.functionField

/-- The completion contains the same characteristic-zero constants. -/
instance fractionField_charZero [CharZero F] : CharZero (FractionField q) :=
  charZero_of_injective_ringHom (algebraMap F (FractionField q)).injective

/-- The original uniformizer stays irreducible in the actual completed stalk. -/
theorem image_irreducible (π : q.localRing) (hπ : Irreducible π) :
    Irreducible (completionMap q π) := AdicCompletion.irreducible_algebraMap q.localRing π hπ

end AlgebraicGeometry.Scheme.RationalPoint.Completion

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Stalk/RationalPointCompletion.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 9eab6dc69a05339ccf4b9e79647fe59a00798374b63143b9b0d1b9772afaa2d7.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
