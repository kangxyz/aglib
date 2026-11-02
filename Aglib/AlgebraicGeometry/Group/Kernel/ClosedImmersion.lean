/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Closedness of the original group-scheme kernel

The unit of a separated group scheme is a closed section. Pulling it back
along the original group morphism makes the existing kernel inclusion a
closed immersion. No finiteness of the multiplication morphism is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.Kernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G E : Grp (Over S)} (p : G ⟶ E)

/-- The actual unit section of the separated target is closed. -/
theorem isClosedImmersion_unit [IsSeparated E.X.hom] :
    IsClosedImmersion (η[E.X]).left := by
  have : IsClosedImmersion ((η[E.X]).left ≫ E.X.hom) := by
    rw [Over.w]
    change IsClosedImmersion (𝟙 S)
    infer_instance
  exact IsClosedImmersion.of_comp _ E.X.hom

/-- The existing kernel inclusion is closed over an arbitrary base. -/
instance inclusion_isClosedImmersion [IsSeparated E.X.hom] :
    IsClosedImmersion (inclusion p).hom.hom.left := by
  let := isClosedImmersion_unit (E := E)
  exact MorphismProperty.of_isPullback (schemeSquare p).flip inferInstance

end AlgebraicGeometry.Scheme.Group.Kernel
