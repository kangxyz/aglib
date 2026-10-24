/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.PullbackAffine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.OpenGluing
public import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Actual module partitions from finite open covers

Finite partitions on a finite retrocompact open cover glue through the original
coefficient-independent geometric construction. The local module restrictions
are transported along its actual maps to the original local strata. In
particular, affine-local constructibility on a qcqs scheme supplies an actual
global partition; a global partition is not an extra premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r v

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Glue finite-type module restrictions on actual finite local partitions
along a finite retrocompact open cover. -/
theorem nonempty_constructiblePartition_of_finite_open_cover {X : Scheme.{u}}
    {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (hretro : ∀ i, IsRetrocompact (U i : Set X))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (F : ModuleSheaf R X)
    (hF : ∀ i, Nonempty (ConstructiblePartition ((moduleInverseImage R (U i).ι).obj F))) :
    Nonempty (ConstructiblePartition F) := by
  let t (i : ι) := Classical.choice (hF i)
  obtain ⟨p, hp⟩ := FiniteLocallyClosedPartition.exists_glue_open_cover U hretro hcover
    (fun i => (t i).toFiniteLocallyClosedPartition)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro k
  obtain ⟨i, j, a, ha⟩ := hp k
  have ha' : (a ≫ (t i).inclusion j) ≫ (U i).ι = p.inclusion k := by
    simpa only [Category.assoc] using ha
  rw [← ha']
  apply (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImageComp R (U i).ι (a ≫ (t i).inclusion j)).app F)).mpr
  apply (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImageComp R ((t i).inclusion j) a).app
      ((moduleInverseImage R (U i).ι).obj F))).mpr
  exact isFiniteTypeLocallyConstant_pullback a ((t i).locally_constant j)

/-- Partitions on affine neighborhoods of every point glue to a global
partition on a qcqs scheme. Only the required finite subcover is chosen. -/
theorem nonempty_constructiblePartition_of_affine_neighborhoods {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (F : ModuleSheaf R X)
    (hF : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (ConstructiblePartition ((moduleInverseImage R U.1.ι).obj F))) :
    Nonempty (ConstructiblePartition F) := by
  classical
  choose U hxU hU using hF
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, ((U x).1 : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set X)) (fun x => (U x).1.isOpen) hcover
  apply nonempty_constructiblePartition_of_finite_open_cover
    (fun x : s => (U x.1).1)
    (fun x => (U x.1).2.isCompact.isRetrocompact (U x.1).1.isOpen) ?_
    F (fun x => hU x.1)
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hxy⟩

/-- The actual affine-local definition produces a global finite partition
on a qcqs scheme, using a finite affine subcover and no Noetherian hypothesis. -/
theorem nonempty_constructiblePartition {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {F : ModuleSheaf R X}
    (hF : IsConstructible F) : Nonempty (ConstructiblePartition F) := by
  let c := X.affineCover.finiteSubcover
  have (i : c.I₀) : IsAffine (c.X i) := by
    change IsAffine (X.affineCover.X _)
    infer_instance
  let U (i : c.I₀) : X.affineOpens :=
    ⟨(c.f i).opensRange, isAffineOpen_opensRange (c.f i)⟩
  apply nonempty_constructiblePartition_of_finite_open_cover (fun i => (U i).1)
    (fun i => (U i).2.isCompact.isRetrocompact (U i).1.isOpen) ?_ F (fun i => hF (U i))
  intro x
  exact ⟨c.idx x, c.covers x⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
