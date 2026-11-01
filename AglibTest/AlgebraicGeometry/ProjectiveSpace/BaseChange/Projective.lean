/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Projective

/-! Projectivity base change uses the original pullback over arbitrary commutative rings. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example {R S : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) [IsHProjective p] (t : Spec S ⟶ Spec R) :
    IsHProjective (pullback.snd p t) := inferInstance

end
