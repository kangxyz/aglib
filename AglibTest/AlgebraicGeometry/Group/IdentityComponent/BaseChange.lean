/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.BaseChange
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# The identity component under field extension

The examples restate that the identity component of the base change of a group scheme locally of
finite type over a field to an extension field is the preimage of the identity component, for the
group structure of the base change, and guard the axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace AglibTest.IdentityComponentBaseChange

open AlgebraicGeometry AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
  (K : Type u) [Field K] [Algebra k K]

/-- `(G_K)⁰` is the preimage of `G⁰`, for the base-changed group structure. -/
theorem identityComponent_baseChange :
    identityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) =
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        identityComponent G :=
  identityComponent_pullback G K

/-- The preimage of `G⁰` is the base change of `G⁰`, so `(G⁰)_K ≅ (G_K)⁰` as schemes. -/
example :
    pullback (identityComponentOver G).hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ
        identityComponent G).toScheme :=
  (isPullback_preimage_identityComponent G K).isoPullback.symm

/-- `(G⁰)_K ≅ (G_K)⁰` as schemes; irreducibility, for example, transfers along it. -/
example [IrreducibleSpace
      (identityComponent
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)).toScheme] :
    IrreducibleSpace
      (pullback (identityComponentOver G).hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}) :=
  (pullbackIdentityComponentIso G K).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

/-- The base change is again a group scheme over `K`. -/
example : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) :=
  inferInstance

/-- The group structure of the base change is that of Aglib's `groupSchemeBaseChange`. -/
example (A : Grp (Over (Spec (.of k)))) :
    ((Scheme.Group.BaseChange.groupSchemeBaseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).functor.obj A).grp =
      Functor.grpObjObj (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (G := A.X) :=
  rfl

/-- info: 'AlgebraicGeometry.Scheme.Group.identityComponent_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identityComponent_pullback

/-- info: 'AlgebraicGeometry.Scheme.Group.isPullback_preimage_identityComponent' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isPullback_preimage_identityComponent

/-- info: 'AglibTest.IdentityComponentBaseChange.identityComponent_baseChange' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identityComponent_baseChange

end AglibTest.IdentityComponentBaseChange
