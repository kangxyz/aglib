/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation along a surjective ring map

A module that is finitely generated over `R'` stays finitely generated over `R` when its scalars
are restricted along a surjective ring map `e : R → R'` (`Module.compHom`). Mathlib has the
submodule analogue `Submodule.FG.restrictScalars_of_surjective`.
-/

@[expose] public section

namespace Module.Finite

/-- A module that is finite over `R'` is finite over `R` along a surjective ring map `R → R'`. -/
theorem compHom_of_surjective {R R' M : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R' M] [Module.Finite R' M] (e : R →+* R') (he : Function.Surjective e) :
    letI := Module.compHom M e
    Module.Finite R M := by
  let := Module.compHom M e
  let := e.toAlgebra
  have : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R') he
  exact Module.Finite.trans R' M

end Module.Finite
