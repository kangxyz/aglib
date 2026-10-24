/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.FiniteType

/-!
# The identity component is geometrically irreducible and of finite type

The examples restate that the identity component of a group scheme locally of finite type over an
arbitrary field is geometrically irreducible, irreducible, quasi-compact, of finite type and
Noetherian, through the instances, and guard the axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace AglibTest.IdentityComponentFiniteType

open AlgebraicGeometry AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]

/-- `G⁰` is geometrically irreducible over `k`. -/
example : GeometricallyIrreducible (identityComponentOver G).hom := inferInstance

/-- `G⁰` is irreducible and quasi-compact, as a scheme and as a subset of `G`. -/
theorem irreducible_and_compact :
    IrreducibleSpace (identityComponent G).toScheme ∧ CompactSpace (identityComponent G).toScheme ∧
      IsIrreducible (identityComponent G : Set G.left) ∧
      IsCompact (identityComponent G : Set G.left) :=
  ⟨inferInstance, inferInstance, isIrreducible_identityComponent G, isCompact_identityComponent G⟩

/-- `G⁰` is of finite type over `k`. -/
theorem finiteType :
    QuasiCompact (identityComponentOver G).hom ∧
      LocallyOfFiniteType (identityComponentOver G).hom :=
  quasiCompact_and_locallyOfFiniteType_identityComponentOver G

/-- `G⁰` is a Noetherian scheme, hence a Noetherian space. -/
example : TopologicalSpace.NoetherianSpace (identityComponent G).toScheme := inferInstance

/-- Base change of `G⁰` to an algebraically closed extension is irreducible. -/
example (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K] :
    IrreducibleSpace (pullback (identityComponentOver G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  irreducibleSpace_pullback_identityComponentOver_of_isAlgClosed G K

/-- Base change of `G⁰` to any extension is irreducible, by geometric irreducibility. -/
example (K : Type u) [Field K] [Algebra k K] :
    IrreducibleSpace (pullback (identityComponentOver G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)

/-- info: 'AlgebraicGeometry.Scheme.Group.geometricallyIrreducible_identityComponentOver' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geometricallyIrreducible_identityComponentOver

/-- info: 'AlgebraicGeometry.Scheme.Group.compactSpace_identityComponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compactSpace_identityComponent

/-- info: 'AlgebraicGeometry.Scheme.Group.quasiCompact_identityComponentOver_hom' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quasiCompact_identityComponentOver_hom

/-- info: 'AlgebraicGeometry.Scheme.Group.isNoetherian_identityComponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isNoetherian_identityComponent

/-- info: 'AglibTest.IdentityComponentFiniteType.irreducible_and_compact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducible_and_compact

end AglibTest.IdentityComponentFiniteType
