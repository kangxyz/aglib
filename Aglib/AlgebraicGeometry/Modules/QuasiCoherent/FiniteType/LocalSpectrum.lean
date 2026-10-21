/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherent coefficients on the actual local-spectrum base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (F : X.Modules) (hF : affineLocallyFiniteType X F) (y : Y)

include hF in
/-- Coherence of the original coefficient after actual local-spectrum base change.
Local Noetherianity of the source follows from properness, not a public premise. -/
theorem affineLocallyFiniteType_fromSpecStalkPullback :
    affineLocallyFiniteType (Limits.pullback f (Y.fromSpecStalk y))
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Y.fromSpecStalk y))).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact affineLocallyFiniteType_pullback (Limits.pullback.fst f (Y.fromSpecStalk y)) hF

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
