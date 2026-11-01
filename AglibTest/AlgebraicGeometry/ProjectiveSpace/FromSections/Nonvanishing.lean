/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Nonvanishing

/-! Original global sections supply one finite-coordinate projective map and its O(1) equation. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example {X : Scheme.{u}} {R : Type u} [CommRing R] [CompactSpace X]
    (p : X ⟶ Spec (.of R)) (L : LineBundle X) {I : Type u}
    (s : I → Γ(L.val, ⊤)) (hcover : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s i)) :
    ∃ (J : Type u) (_ : Finite J) (f : X ⟶ ProjectiveSpace R J),
      f ≫ ProjectiveSpace.toSpec R J = p ∧
        Nonempty ((Scheme.Modules.pullback f).obj (ProjectiveSpace.twistingSheaf R J 1) ≅ L.val) :=
  ProjectiveSpace.FromSections.exists_projectiveMap_of_nonvanishing_cover p L s hcover

end

/--
info: 'AlgebraicGeometry.ProjectiveSpace.FromSections.exists_projectiveMap_of_nonvanishing_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.FromSections.exists_projectiveMap_of_nonvanishing_cover
