/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Connected.LocallyConnected
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Locally Noetherian schemes are locally connected

The underlying space of a locally Noetherian scheme is locally connected
(`AlgebraicGeometry.IsLocallyNoetherian.locallyConnectedSpace`; Stacks Project, Tag 04MF): every
point has an affine open neighbourhood, whose ring of sections is Noetherian, so the neighbourhood
is a Noetherian space (Mathlib's `AlgebraicGeometry.noetherianSpace_of_isAffineOpen`), and
`locallyConnectedSpace_of_forall_exists_noetherianSpace` applies. Hence the connected components
of a locally Noetherian scheme are open and closed (Mathlib's `isClopen_connectedComponent`).
-/

@[expose] public section

namespace AlgebraicGeometry

/-- **A locally Noetherian scheme is locally connected** (Stacks 04MF). -/
instance (priority := 100) IsLocallyNoetherian.locallyConnectedSpace (X : Scheme)
    [IsLocallyNoetherian X] : LocallyConnectedSpace X := by
  refine locallyConnectedSpace_of_forall_exists_noetherianSpace fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by simp)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨U, U.isOpen.mem_nhds hxU, noetherianSpace_of_isAffineOpen U hU⟩

end AlgebraicGeometry
