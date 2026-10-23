/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Arbitrary small affine-open covering families

Every open is covered by its actual affine subopens, with indices in the
scheme universe. No quasi-compactness, separatedness or finite-cover
hypothesis is imposed. These families detect exactness of restricted
resolutions in the all-scheme cohomology comparison.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (W : X.Opens)

/-- The original affine subopens of a given open, with their inclusion arrows. -/
def affineSubopenFamily : { V : X.affineOpens // V.val ≤ W } → Over W :=
  fun V => Over.mk (homOfLE V.property)

/-- The actual affine subopen family covers even a non-quasi-compact open. -/
theorem affineSubopenFamily_covering :
    Sieve.ofArrows (fun i => (affineSubopenFamily X W i).left)
      (fun i => (affineSubopenFamily X W i).hom) ∈ Opens.grothendieckTopology X W := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  refine ⟨V, homOfLE hVW, ?_, hxV⟩
  exact Sieve.ofArrows_mk _ _ (⟨⟨V, hV⟩, hVW⟩ : { V : X.affineOpens // V.val ≤ W })

/-- The covering-object-basis input for the original sheaf exactness criterion. -/
theorem exists_affineOpen_covering_family :
    ∃ (ι : Type u) (U : ι → Over W),
      Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈
        Opens.grothendieckTopology X W ∧ ∀ i, IsAffineOpen (U i).left :=
  ⟨_, affineSubopenFamily X W, affineSubopenFamily_covering X W, fun i => i.val.property⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
