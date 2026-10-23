/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.LocallyClosed

/-!
# Affine neighborhoods of finite-type field points

For an actual locally finite-type morphism `c : Spec K ⟶ S`, with `K` a field
and `S` locally Noetherian, its singleton image is locally closed. There is an
affine open neighborhood through which the same morphism factors and in which
its point is closed and the factorization is finite. The canonical map from
the residue field of the image point to the full original field `K` is finite,
without a Noetherian hypothesis.

The current consumer is the local surface-contraction construction: the base
must be shrunk before a curve over this point can be treated as proper over it.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

private lemma exists_isLocallyClosed_subset_of_isConstructible
    {T : Type*} [TopologicalSpace T] {s : Set T} (hs : IsConstructible s)
    {x : T} (hx : x ∈ s) :
    ∃ t : Set T, IsLocallyClosed t ∧ x ∈ t ∧ t ⊆ s := by
  have h : ∀ x ∈ s, ∃ t : Set T, IsLocallyClosed t ∧ x ∈ t ∧ t ⊆ s := by
    clear hx x
    induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
    | isSublattice =>
      exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
        fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
    | bot_mem => exact ⟨isOpen_empty, .empty⟩
    | top_mem => exact ⟨isOpen_univ, .univ⟩
    | sdiff U hU V hV =>
      exact fun x hx ↦ ⟨U \ V, ⟨U, Vᶜ, hU.1, hV.1.isClosed_compl, rfl⟩,
        hx, Set.Subset.rfl⟩
    | sup U _ V _ hU hV =>
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨t, ht, hxt, htU⟩ := hU x hx
        exact ⟨t, ht, hxt, htU.trans Set.subset_union_left⟩
      · obtain ⟨t, ht, hxt, htV⟩ := hV x hx
        exact ⟨t, ht, hxt, htV.trans Set.subset_union_right⟩
  exact h x hx

private lemma isLocallyClosed_singleton_of_isLocallyConstructible
    {T : Type*} [TopologicalSpace T] (x : T)
    (h : IsLocallyConstructible ({x} : Set T)) :
    IsLocallyClosed ({x} : Set T) := by
  obtain ⟨U, hxU, hU, hs⟩ := h x
  have hx : x ∈ U := mem_of_mem_nhds hxU
  obtain ⟨t, ht, hxt, hts⟩ :=
    exists_isLocallyClosed_subset_of_isConstructible hs
      (show (⟨x, hx⟩ : U) ∈ (Subtype.val ⁻¹' {x}) from rfl)
  have heq : t = ({⟨x, hx⟩} : Set U) := by
    apply Set.Subset.antisymm
    · intro y hy
      apply Set.mem_singleton_iff.mpr
      exact Subtype.ext (hts hy)
    · exact Set.singleton_subset_iff.mpr hxt
  rw [heq] at ht
  have hImage := ht.image hU.isOpenEmbedding_subtypeVal.isEmbedding.isInducing
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hU.isLocallyClosed)
  simpa only [Set.image_singleton] using hImage

namespace AlgebraicGeometry.Scheme

private lemma range_fieldPoint {K : Type u} [Field K] {S : Scheme.{u}}
    (c : Spec (CommRingCat.of K) ⟶ S) :
    Set.range c = {c (IsLocalRing.closedPoint K)} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact congrArg c (Subsingleton.elim _ _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-- The singleton image of a locally finite-type field point in a locally
Noetherian scheme is locally closed. -/
theorem Hom.isLocallyClosed_range_of_field
    {K : Type u} [Field K] {S : Scheme.{u}} [IsLocallyNoetherian S]
    (c : Spec (CommRingCat.of K) ⟶ S) [LocallyOfFiniteType c] :
    IsLocallyClosed (Set.range c) := by
  rw [range_fieldPoint c]
  apply isLocallyClosed_singleton_of_isLocallyConstructible
  simpa only [Set.image_univ, range_fieldPoint] using
    c.isLocallyConstructible_image IsLocallyConstructible.univ

/-- An actual finite-type field point factors through an affine open in which
its image point is closed. The factorization retains the original field. -/
theorem Hom.exists_affine_closedPoint_lift_of_field
    {K : Type u} [Field K] {S : Scheme.{u}} [IsLocallyNoetherian S]
    (c : Spec (CommRingCat.of K) ⟶ S) [LocallyOfFiniteType c] :
    ∃ (V : S.Opens) (_ : IsAffineOpen V)
      (cV : Spec (CommRingCat.of K) ⟶ V),
      cV ≫ V.ι = c ∧ IsClosed ({cV (IsLocalRing.closedPoint K)} : Set V) := by
  let x : S := c (IsLocalRing.closedPoint K)
  have hloc : IsLocallyClosed ({x} : Set S) := by
    simpa only [range_fieldPoint] using c.isLocallyClosed_range_of_field
  obtain ⟨U, Z, hU, hZ, hUZ⟩ := hloc
  have hxUZ : x ∈ U ∩ Z := hUZ ▸ Set.mem_singleton x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⟨U, hU⟩ : S.Opens) from hxUZ.1)
  have hrange : Set.range c ⊆ Set.range V.ι := by
    rw [range_fieldPoint, Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hxV
  let cV := IsOpenImmersion.lift V.ι c hrange
  have hfac : cV ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hcV : (cV (IsLocalRing.closedPoint K)).val = x := by
    change (cV ≫ V.ι) (IsLocalRing.closedPoint K) = x
    rw [hfac]
  have heq : (Subtype.val : V → S) ⁻¹' Z =
      ({cV (IsLocalRing.closedPoint K)} : Set V) := by
    ext y
    constructor
    · intro hy
      have hyx : (y : S) ∈ ({x} : Set S) := by
        rw [hUZ]
        exact ⟨hVU y.property, hy⟩
      exact Set.mem_singleton_iff.mpr
        (Subtype.ext ((Set.mem_singleton_iff.mp hyx).trans hcV.symm))
    · intro hy
      change (y : S) ∈ Z
      have hyx : (y : S) = x :=
        (congrArg (fun y : V ↦ (y : S)) (Set.mem_singleton_iff.mp hy)).trans hcV
      exact hyx.symm ▸ hxUZ.2
  exact ⟨V, hV, cV, hfac, heq ▸ hZ.preimage continuous_subtype_val⟩

/-- The canonical map from the actual image-point residue field to the full
original field of a locally finite-type point is finite. -/
theorem Hom.finite_descResidueField_of_field
    {K : Type u} [Field K] {S : Scheme.{u}}
    (c : Spec (CommRingCat.of K) ⟶ S) [LocallyOfFiniteType c] :
    (S.descResidueField (Scheme.stalkClosedPointTo c)).hom.Finite := by
  let φ := S.descResidueField (Scheme.stalkClosedPointTo c)
  have hcomp : LocallyOfFiniteType
      (Spec.map φ ≫ S.fromSpecResidueField (c (IsLocalRing.closedPoint K))) := by
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    infer_instance
  let : LocallyOfFiniteType (Spec.map φ) :=
    locallyOfFiniteType_of_comp (Spec.map φ)
      (S.fromSpecResidueField (c (IsLocalRing.closedPoint K)))
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  exact RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hφ

/-- A locally finite-type field point with closed image is an actual finite
morphism, using its canonical residue-field factorization. -/
theorem Hom.isFinite_of_field_of_isClosed_image
    {K : Type u} [Field K] {S : Scheme.{u}}
    (c : Spec (CommRingCat.of K) ⟶ S) [LocallyOfFiniteType c]
    (hclosed : IsClosed ({c (IsLocalRing.closedPoint K)} : Set S)) :
    IsFinite c := by
  let φ := S.descResidueField (Scheme.stalkClosedPointTo c)
  have hfac : Spec.map φ ≫
      S.fromSpecResidueField (c (IsLocalRing.closedPoint K)) = c :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S c
  let : IsFinite (Spec.map φ) :=
    (IsFinite.SpecMap_iff φ).mpr c.finite_descResidueField_of_field
  let : IsClosedImmersion (S.fromSpecResidueField (c (IsLocalRing.closedPoint K))) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  have hfinite : IsFinite (Spec.map φ ≫
      S.fromSpecResidueField (c (IsLocalRing.closedPoint K))) := inferInstance
  exact hfac ▸ hfinite

/-- After shrinking the actual base to an affine open, the original field
point is finite over that open. -/
theorem Hom.exists_affine_finite_lift_of_field
    {K : Type u} [Field K] {S : Scheme.{u}} [IsLocallyNoetherian S]
    (c : Spec (CommRingCat.of K) ⟶ S) [LocallyOfFiniteType c] :
    ∃ (V : S.Opens) (_ : IsAffineOpen V)
      (cV : Spec (CommRingCat.of K) ⟶ V), cV ≫ V.ι = c ∧ IsFinite cV := by
  obtain ⟨V, hV, cV, hfac, hclosed⟩ := c.exists_affine_closedPoint_lift_of_field
  have : LocallyOfFiniteType (cV ≫ V.ι) := hfac.symm ▸ ‹LocallyOfFiniteType c›
  let : LocallyOfFiniteType cV := locallyOfFiniteType_of_comp cV V.ι
  exact ⟨V, hV, cV, hfac, cV.isFinite_of_field_of_isClosed_image hclosed⟩

end AlgebraicGeometry.Scheme
