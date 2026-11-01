/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # A genuine finite locally constant generic open

The original stratum containing the generic point has dense locally closed
image. Its coborder is exactly that image. The original closed-immersion
factor is surjective onto a reduced open of the integral base, hence an
isomorphism. Thus that same stratum is an actual open immersion, and its
original coefficient restriction is finite locally constant. Reducedness of
the target is essential in this argument.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- The original generic stratum of a genuine constructible partition on an
integral scheme is a nonempty open with finite locally constant restriction. -/
theorem exists_nonempty_finiteLocallyConstant_open_of_partition
    {X : Scheme.{u}} [IsIntegral X] {F : AbelianSheaf.{u, u + 1} X}
    (t : ConstructiblePartition F) :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsOpenImmersion j ∧ Nonempty S ∧
      IsFiniteLocallyConstant ((inverseImage j).obj F) := by
  obtain ⟨k, z, hz⟩ := t.covers (genericPoint X)
  let i := t.inclusion k
  have : IsImmersion i := t.immersion k
  have hclosure : closure (Set.range i) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure X]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨z, hz⟩)
  have hCoborder : (i.coborderRange : Set X) = Set.range i := by
    change coborder (Set.range i) = Set.range i
    rw [coborder_eq_union_closure_compl, hclosure, Set.compl_univ, Set.union_empty]
  have : Surjective i.liftCoborder := by
    constructor
    intro x
    have hx : x.1 ∈ Set.range i := by
      rw [← hCoborder]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply i.coborderRange.ι.isOpenEmbedding.injective
    change (i.liftCoborder ≫ i.coborderRange.ι) y = x.1
    rw [i.liftCoborder_ι]
    exact hy
  have : IsReduced i.coborderRange.toScheme := inferInstance
  have : IsIso i.liftCoborder := isIso_of_isClosedImmersion_of_surjective i.liftCoborder
  have : IsOpenImmersion i := by
    rw [← i.liftCoborder_ι]
    infer_instance
  exact ⟨t.stratum k, i, inferInstance, ⟨z⟩, t.locally_constant k⟩

/-- An original constructible abelian sheaf on an integral affine scheme is
finite locally constant on a genuine nonempty open. -/
theorem exists_nonempty_finiteLocallyConstant_open
    {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsConstructible F) :
    ∃ (S : Scheme.{u}) (j : S ⟶ X), IsOpenImmersion j ∧ Nonempty S ∧
      IsFiniteLocallyConstant ((inverseImage j).obj F) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have : IsIntegral U.1.toScheme := IsIntegral.of_isIso X.topIso.inv
  obtain ⟨t⟩ := hF U
  obtain ⟨S, j, hj, hS, hloc⟩ := exists_nonempty_finiteLocallyConstant_open_of_partition t
  have : IsOpenImmersion j := hj
  refine ⟨S, j ≫ U.1.ι, inferInstance, hS, ?_⟩
  exact (isFiniteLocallyConstant_iff_of_iso ((inverseImageComp U.1.ι j).app F)).mpr hloc

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
