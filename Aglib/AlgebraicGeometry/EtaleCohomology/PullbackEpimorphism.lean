/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage

/-! # Original inverse-image preservation of epimorphisms

The native inverse-image functor preserves epis before specializing the
source coefficient arrow to any geometric chart or comparison model.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original pullback of an arbitrary epimorphism of abelian sheaves is epic. -/
theorem inverseImage_map_epi {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F G : AbelianSheaf.{u, u + 1} X} (s : F ⟶ G) [Epi s] :
    Epi ((inverseImage g).map s) := inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology
