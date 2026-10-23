/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finite actual constructible covers on qcqs schemes

Affine-local constructibility gives a finite family of actual constructible
locally closed subschemes covering a qcqs scheme, with finite locally constant
original coefficient restrictions. A finite affine subcover and the original
local partitions construct the family. The resulting pieces can overlap; this
is a cover, not a disjoint partition. Quasi-separatedness makes the chosen
affine open immersions retrocompact, so the original constructible ranges remain
constructible after composition into the base.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- A finite covering family of actual constructible locally closed subschemes
with finite locally constant original restrictions. Pieces need not be disjoint. -/
structure FiniteLocallyClosedCover {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) where
  /-- The actual finite indexing type in the scheme universe. -/
  index : Type u
  /-- The family has finitely many pieces. -/
  finite_index : Finite index
  /-- The actual locally closed source schemes. -/
  stratum : index → Scheme.{u}
  /-- Their original structure morphisms to the base. -/
  inclusion : ∀ i, stratum i ⟶ X
  /-- Every structure morphism is an immersion. -/
  immersion : ∀ i, IsImmersion (inclusion i)
  /-- Every original image is constructible in the base. -/
  constructible_range : ∀ i, Topology.IsConstructible (Set.range (inclusion i))
  /-- The actual pieces cover every original point. -/
  covers : ∀ x : X, ∃ i, ∃ y : stratum i, inclusion i y = x
  /-- The restriction is the original scheme inverse image. -/
  locally_constant : ∀ i, IsFiniteLocallyConstant ((inverseImage (inclusion i)).obj F)

/-- The actual affine-local definition produces a finite constructible
locally closed cover on a qcqs scheme. No global partition is assumed. -/
def finiteLocallyClosedCover {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    FiniteLocallyClosedCover F := by
  let c := X.affineCover.finiteSubcover
  have (i : c.I₀) : IsAffine (c.X i) := by
    change IsAffine (X.affineCover.X _)
    infer_instance
  let U (i : c.I₀) : X.affineOpens :=
    ⟨(c.f i).opensRange, isAffineOpen_opensRange (c.f i)⟩
  let t (i : c.I₀) := Classical.choice (hF (U i))
  refine {
    index := Σ i : c.I₀, Fin (t i).count
    finite_index := inferInstance
    stratum := fun q => (t q.1).stratum q.2
    inclusion := fun q => (t q.1).inclusion q.2 ≫ (U q.1).1.ι
    immersion := ?_
    constructible_range := ?_
    covers := ?_
    locally_constant := ?_ }
  · intro q
    have : IsImmersion ((t q.1).inclusion q.2) := (t q.1).immersion q.2
    infer_instance
  · intro q
    change Topology.IsConstructible
      (Set.range ((U q.1).1.ι ∘ (t q.1).inclusion q.2))
    rw [Set.range_comp]
    apply ((t q.1).constructible_range q.2).image_of_isOpenEmbedding
      (U q.1).1.ι.isOpenEmbedding
    rw [Scheme.Opens.range_ι]
    exact (U q.1).2.isCompact.isRetrocompact (U q.1).1.isOpen
  · intro x
    let i := c.idx x
    have hx : x ∈ (U i).1 := c.covers x
    obtain ⟨k, z, hz⟩ := (t i).covers ⟨x, hx⟩
    refine ⟨⟨i, k⟩, z, ?_⟩
    exact congrArg (U i).1.ι hz
  · intro q
    exact (isFiniteLocallyConstant_iff_of_iso
      ((inverseImageComp (U q.1).1.ι ((t q.1).inclusion q.2)).app F)).mpr
        ((t q.1).locally_constant q.2)

/-- The chosen cover witnesses existence with the exact original coefficient
restrictions, at the standard qcqs range. -/
theorem nonempty_finiteLocallyClosedCover {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsConstructible F) :
    Nonempty (FiniteLocallyClosedCover F) := ⟨finiteLocallyClosedCover F hF⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
