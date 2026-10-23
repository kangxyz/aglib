/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Quasi-coherence in short exact sequences

In a short exact sequence `0 → K → M → N → 0` of module sheaves on a scheme with `M` and `N`
quasi-coherent, `K` is quasi-coherent (`isQuasicoherent_X₁_of_shortExact`): it is isomorphic to the
kernel of `M ⟶ N`, which is quasi-coherent (`QuasiCoherent.quasicoherent_kernel`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The first term of a short exact sequence is quasi-coherent when the other two are. -/
theorem isQuasicoherent_X₁_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₁.IsQuasicoherent := by
  have := QuasiCoherent.quasicoherent_kernel S.g
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hS.fIsKernel) this

end AlgebraicGeometry.Scheme.Modules
