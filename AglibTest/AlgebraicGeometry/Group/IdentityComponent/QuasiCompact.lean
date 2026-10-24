/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.QuasiCompact

/-!
# Quasi-compactness of the identity component over an algebraically closed field

The examples restate that the division map of a group scheme over a field is open, through the
shear automorphism, that an irreducible group scheme locally of finite type over an algebraically
closed field is quasi-compact, and that the identity component is quasi-compact, and guard the
axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.IdentityComponentQuasiCompact

open AlgebraicGeometry AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The shear automorphism followed by the first projection is the division map. -/
example : (GrpObj.shearIso G).hom ≫ fst G G = fst G G / snd G G := GrpObj.shearIso_hom_fst G

/-- The shear automorphism keeps the second coordinate. -/
example : (GrpObj.shearIso G).hom ≫ snd G G = snd G G := GrpObj.shearIso_hom_snd G

/-- The division map `(a, b) ↦ a b⁻¹` is open on underlying spaces. -/
theorem isOpenMap_div : IsOpenMap (fst G G / snd G G).left := isOpenMap_fst_div_snd_left G

variable [LocallyOfFiniteType G.hom] [IsAlgClosed k]

/-- An irreducible group scheme locally of finite type over an algebraically closed field is
quasi-compact. -/
example [IrreducibleSpace G.left] : CompactSpace G.left :=
  compactSpace_of_irreducibleSpace_of_isAlgClosed G

/-- `G⁰` is quasi-compact over an algebraically closed field. -/
theorem compact : CompactSpace (identityComponent G).toScheme :=
  compactSpace_identityComponent_of_isAlgClosed G

/-- info: 'AlgebraicGeometry.Scheme.Group.isOpenMap_fst_div_snd_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isOpenMap_fst_div_snd_left

/-- info: 'AlgebraicGeometry.Scheme.Group.compactSpace_of_irreducibleSpace_of_isAlgClosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compactSpace_of_irreducibleSpace_of_isAlgClosed

/-- info: 'AlgebraicGeometry.Scheme.Group.compactSpace_identityComponent_of_isAlgClosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compactSpace_identityComponent_of_isAlgClosed

/-- info: 'AglibTest.IdentityComponentQuasiCompact.compact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compact

end AglibTest.IdentityComponentQuasiCompact
