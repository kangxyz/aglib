/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinEtalePullback
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericPoints

/-!
# Actual generic points under etale tests

Flat maps carry generic points to generic points. Points of the actual
Artinian pullback over a generic stalk project to generic points of the test.
These statements use the original scheme maps, not residue-field surrogates.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {U X : Scheme.{u}} (f : U ⟶ X) (η : genericPoints X)

/-- Every point in the actual Artinian generic pullback projects to a generic point of U. -/
theorem genericEtaleComponent_projection_generic [IsLocallyNoetherian X]
    [Etale f] [QuasiCompact f] (p : genericEtaleComponent f η) :
    (pullback.fst f (X.fromSpecStalk η.val)) p ∈ genericPoints U := by
  let := genericEtaleComponent_isArtinian f η
  have hp : p ∈ genericPoints (genericEtaleComponent f η) := by
    apply mem_genericPoints_of_isMax
    intro z hz
    have he : z = p := specializes_iff_eq.mp hz
    subst z
    exact specializes_rfl
  let : Flat (pullback.fst f (X.fromSpecStalk η.val)) := genericEtaleComponent_flat f η
  exact genericPoint_map_flat _ ⟨p, hp⟩

/-- The projected point lies over precisely the designated original generic point. -/
theorem genericEtaleComponent_projection_image (p : genericEtaleComponent f η) :
    f ((pullback.fst f (X.fromSpecStalk η.val)) p) = η.val := by
  have hp : (X.fromSpecStalk η.val) ((pullback.snd f (X.fromSpecStalk η.val)) p) = η.val := by
    have hmem : (X.fromSpecStalk η.val) ((pullback.snd f (X.fromSpecStalk η.val)) p) ∈
        Set.range (X.fromSpecStalk η.val) := ⟨_, rfl⟩
    rw [genericArtinComponent_range X η] at hmem
    exact hmem
  exact (congrArg (fun g : genericEtaleComponent f η ⟶ X => g p)
    (pullback.condition (f := f) (g := X.fromSpecStalk η.val))).trans hp

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
