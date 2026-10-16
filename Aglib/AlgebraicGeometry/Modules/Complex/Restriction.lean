/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Homology.Additive

/-!
# Composition of ordinary module-complex restriction

Relocated from `Aglib/AlgebraicGeometry/Modules/Perfect/LocalRestriction.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `427c224a2e1080a356308dc5dfa3cd61cbbaa339d138d0a1a058f2e3c7f2adbc`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable {V U X : Scheme.{u}}

/-- Equality of open immersions gives equality of their restriction functors. -/
theorem restrict_congr {f g : U ⟶ X} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : restrict f = restrict g := by
  subst g
  rfl

/-- Cochain restriction respects composition up to the actual sheaf
restriction isomorphism. -/
def restrictCompIso (f : V ⟶ U) (g : U ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrict g ⋙ restrict f ≅ restrict (f ≫ g) :=
  Functor.mapHomologicalComplexCompIso (Scheme.Modules.restrictFunctorComp f g).symm _

end AlgebraicGeometry.Scheme.Modules.Complex
