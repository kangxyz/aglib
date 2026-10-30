/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Flat.Descent

/-! Descent recovers flatness of the actual original map in a pullback. -/

@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) [Surjective g] [Flat g] [QuasiCompact g] [Flat b] : Flat f :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end
