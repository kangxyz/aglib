/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyConnected

/-!
# Locally Noetherian schemes are locally connected

The examples restate Stacks 04MF for locally Noetherian schemes, its consequence that connected
components are open and closed, and the case of a scheme locally of finite type over a field, and
guard the axioms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.SchemeLocallyConnected

/-- Stacks 04MF for schemes. -/
theorem locallyConnected (X : Scheme.{u}) [IsLocallyNoetherian X] : LocallyConnectedSpace X :=
  inferInstance

/-- The connected components of a locally Noetherian scheme are clopen. -/
theorem isClopen (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    IsClopen (connectedComponent x) :=
  isClopen_connectedComponent

/-- A scheme locally of finite type over a field is locally connected. -/
theorem locallyConnected_of_locallyOfFiniteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : LocallyConnectedSpace X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  inferInstance

/-- info: 'AlgebraicGeometry.IsLocallyNoetherian.locallyConnectedSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsLocallyNoetherian.locallyConnectedSpace

/-- info: 'AglibTest.SchemeLocallyConnected.isClopen' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.SchemeLocallyConnected.isClopen

/-- info: 'AglibTest.SchemeLocallyConnected.locallyConnected_of_locallyOfFiniteType' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.SchemeLocallyConnected.locallyConnected_of_locallyOfFiniteType

end AglibTest.SchemeLocallyConnected
