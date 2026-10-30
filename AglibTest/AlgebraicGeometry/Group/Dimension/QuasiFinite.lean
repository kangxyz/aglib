/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension.QuasiFinite

/-!
# Consumer checks for actual group unit dimensions

The locally quasi-finite comparison and regularity criterion use the actual unit stalks.
Target smoothness and target properness are conclusions of later geometric arguments.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField

universe u

namespace AglibTest.GroupDimensionQuasiFinite

example {k : Type u} [Field k] (G H : FScheme k)
    [GrpObj G] [MonObj H] [Smooth G.hom] [PreconnectedSpace G.left]
    [LocallyOfFiniteType H.hom] (f : G ⟶ H) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hcot : Module.finrank k (Cotangent.Space η[H]) ≤
      Module.finrank k (Cotangent.Space η[G])) :
    ringKrullDim (H.left.presheaf.stalk (unitPoint H)) =
        Module.finrank k (Cotangent.Space η[G]) ∧
      Module.finrank k (Cotangent.Space η[H]) = Module.finrank k (Cotangent.Space η[G]) ∧
      IsRegularLocalRing (H.left.presheaf.stalk (unitPoint H)) :=
  unit_dimension_cotangent_and_regular_of_locallyQuasiFinite G H f hcot

/--
info: 'AlgebraicGeometry.Scheme.Group.hom_unitPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.hom_unitPoint

/--
info: 'AlgebraicGeometry.Scheme.Group.finrank_residueCotangent_eq_finrank_identityCotangent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.finrank_residueCotangent_eq_finrank_identityCotangent

/--
info: 'AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_le_finrank_identityCotangent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_le_finrank_identityCotangent

/--
info: 'AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_le_of_locallyQuasiFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_le_of_locallyQuasiFinite

/--
info: 'AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_eq_finrank_identityCotangent_of_preconnected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.ringKrullDim_unit_eq_finrank_identityCotangent_of_preconnected

/--
info: 'AlgebraicGeometry.Scheme.Group.unit_dimension_cotangent_and_regular_of_locallyQuasiFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.unit_dimension_cotangent_and_regular_of_locallyQuasiFinite

end AglibTest.GroupDimensionQuasiFinite
