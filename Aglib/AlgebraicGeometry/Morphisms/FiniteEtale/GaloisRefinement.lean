/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances

/-! # Actual Galois refinements of nonempty finite etale covers

Over a connected scheme, a nonempty actual finite etale cover receives a map
from an actual connected Galois finite etale cover. The latter's structural
map is surjective. The map to the original cover is not asserted surjective,
since that original cover may be disconnected. This is a geometric cover
refinement, not an equivalence for arbitrary module-valued local systems.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- A nonempty actual finite etale cover over a connected scheme has an
actual connected Galois refinement surjecting onto the original base. -/
theorem exists_galois_refinement {X : Scheme.{u}} [ConnectedSpace X]
    (Y : Scheme.FiniteEtale X) [Nonempty Y.obj.left] :
    ∃ (Z : Scheme.FiniteEtale X) (_ : Z ⟶ Y),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let s := algebraicClosureResiduePoint X x
  have hY : Nonempty ((fiberToFinite s).obj Y) := nonempty_fiber_of_nonempty_cover s Y
  obtain ⟨Z, f, hZ⟩ :=
    PreGaloisCategory.exists_hom_from_galois_of_fiber_nonempty (fiberToFinite s) Y hY
  have : PreGaloisCategory.IsGalois Z := hZ
  have : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  have hsurj : Surjective Z.obj.hom := ⟨Set.range_eq_univ.mp
    ((structural_range_isClopen Z).eq_univ (Set.range_nonempty _))⟩
  exact ⟨Z, f, hZ, inferInstance, hsurj⟩

end AlgebraicGeometry.Scheme.FiniteEtale
