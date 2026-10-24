/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Geometrically.Connected.RationalPoint

/-!
# A connected scheme with a rational point is geometrically connected

The examples restate the rational-point case of Stacks 04KV, connectedness over integral
extensions and over arbitrary field extensions, and the one-point fibre, and guard the axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.RationalPointGeometricallyConnected

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- Stacks 04KV, rational-point case, with no finiteness hypothesis. -/
theorem geometricallyConnected [ConnectedSpace Y] (o : Spec (.of k) ⟶ Y) (ho : o ≫ q = 𝟙 _) :
    GeometricallyConnected q :=
  Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section q o ho

/-- The base change to the algebraic closure is connected. -/
theorem connectedSpace_algebraicClosure [ConnectedSpace Y] (o : Spec (.of k) ⟶ Y)
    (ho : o ≫ q = 𝟙 _) :
    ConnectedSpace
      (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :
        Scheme.{u}) :=
  Scheme.Geometrically.connectedSpace_pullback_of_section q (AlgebraicClosure k) o ho

/-- The base change to an arbitrary field extension is connected. -/
theorem connectedSpace_fieldExtension [ConnectedSpace Y] (o : Spec (.of k) ⟶ Y)
    (ho : o ≫ q = 𝟙 _) (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  Scheme.Geometrically.connectedSpace_extension_of_connected_algebraicClosure k K q
    (connectedSpace_algebraicClosure q o ho)

/-- The spectrum of the field itself, with the identity section. -/
example : GeometricallyConnected (𝟙 (Spec (.of k))) :=
  Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section _ (𝟙 _) (by simp)

/-- info: 'AlgebraicGeometry.Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section

/-- info: 'AlgebraicGeometry.Scheme.Geometrically.connectedSpace_pullback_of_section' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Geometrically.connectedSpace_pullback_of_section

/-- info: 'AlgebraicGeometry.Scheme.Geometrically.subsingleton_preimage_of_section' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Geometrically.subsingleton_preimage_of_section

/-- info: 'AglibTest.RationalPointGeometricallyConnected.connectedSpace_fieldExtension' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.RationalPointGeometricallyConnected.connectedSpace_fieldExtension

end AglibTest.RationalPointGeometricallyConnected
