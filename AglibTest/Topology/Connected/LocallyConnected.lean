/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Topology.Connected.LocallyConnected

/-!
# Locally Noetherian spaces are locally connected

The examples restate Stacks 04MF for spaces whose points have Noetherian neighbourhoods, and the
openness and clopenness of the connected components of a Noetherian space, and guard the axioms.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace AglibTest.NoetherianLocallyConnected

variable {X : Type*} [TopologicalSpace X]

/-- Stacks 04MF: a point-wise Noetherian space is locally connected. -/
theorem locallyConnected (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) :
    LocallyConnectedSpace X :=
  locallyConnectedSpace_of_forall_exists_noetherianSpace h

/-- The connected components of a Noetherian space are clopen, through the instance. -/
theorem isClopen [NoetherianSpace X] (x : X) : IsClopen (connectedComponent x) :=
  isClopen_connectedComponent

/-- An open subspace of a Noetherian space has open connected components in the ambient space. -/
theorem isOpen_connectedComponentIn [NoetherianSpace X] {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

example [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) :=
  NoetherianSpace.isOpen_connectedComponent x

/-- info: 'locallyConnectedSpace_of_forall_exists_noetherianSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms locallyConnectedSpace_of_forall_exists_noetherianSpace

/-- info: 'TopologicalSpace.NoetherianSpace.isOpen_connectedComponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.NoetherianSpace.isOpen_connectedComponent

/-- info: 'AglibTest.NoetherianLocallyConnected.isClopen' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.NoetherianLocallyConnected.isClopen

end AglibTest.NoetherianLocallyConnected
