/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.CoverComponents
public import Aglib.AlgebraicGeometry.Gluing.FiniteClosedCover
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.TwoPointSubscheme
public import Aglib.AlgebraicGeometry.Limits.SpecProducts

/-!
# Actual partial and pairwise intersections of polygon components

Finite subsets map into the actual complementary union through their exact kernel inclusions.
Two-point full intersections prove reducedness of the partial overlaps. The same literal endpoint
maps identify adjacent pairs at n greater than two and both distinct intersections in the two-gon,
retaining the reversed endpoint order on the second component.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/Incidence/CyclicClosedCover.lean`: source ranges [[34, 149], [171, 609]];
SHA-256 `3255652277d7f78785d4d1643de7e9048f11b394d71de3bb44b6d094cbd1bd0e`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open Scheme.IdealSheafData Scheme.FiniteClosedCover
universe u

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

lemma otherGlobalIdeal_le_finiteUnion (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    otherGlobalIdeal k n i ≤ unionIdeal (componentTarget k n) S := by
  rw [otherGlobalIdeal_eq_iInf]
  apply le_iInf
  intro j
  exact iInf_le_of_le ⟨j.val, fun h => hi (h ▸ j.property)⟩ le_rfl

/-- Literal finite-union factor into the permanent native complementary scheme. -/
def finiteUnionToOther (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    unionScheme (componentTarget k n) S ⟶ otherGlobalScheme k n i :=
  Scheme.IdealSheafData.inclusion (otherGlobalIdeal_le_finiteUnion k n S i hi)

@[reassoc (attr := simp)] lemma finiteUnionToOther_triangle
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finiteUnionToOther k n S i hi ≫ otherGlobalInclusion k n i =
      unionMap (componentTarget k n) S := Scheme.IdealSheafData.inclusion_subschemeι _

/-- The actual finite union is a closed subscheme of its full complement. -/
instance finiteUnionToOther_closed (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    IsClosedImmersion (finiteUnionToOther k n S i hi) := by
  have : IsClosedImmersion (finiteUnionToOther k n S i hi ≫ otherGlobalInclusion k n i) := by
    rw [finiteUnionToOther_triangle]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (otherGlobalInclusion k n i)

/-- The actual finite-union/component fibre product in the finite descent order. -/
abbrev finitePartialIntersection (S : Finset (Fin n)) (i : Fin n) : Scheme.{u} :=
  pullback (unionMap (componentTarget k n) S) (componentTarget k n i)

/-- First keep the finite-descent order: union first, selected component second. -/
def finitePartialToOtherOrder (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialIntersection k n S i ⟶
      pullback (otherGlobalInclusion k n i) (componentTarget k n i) :=
  pullback.lift (pullback.fst _ _ ≫ finiteUnionToOther k n S i hi)
    (pullback.snd _ _) (by
      simp only [Category.assoc, finiteUnionToOther_triangle]
      exact pullback.condition)

@[reassoc (attr := simp)] lemma finitePartialToOtherOrder_fst
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialToOtherOrder k n S i hi ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ finiteUnionToOther k n S i hi := pullback.lift_fst ..

@[reassoc (attr := simp)] lemma finitePartialToOtherOrder_snd
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialToOtherOrder k n S i hi ≫ pullback.snd _ _ =
      pullback.snd (unionMap (componentTarget k n) S) (componentTarget k n i) :=
  pullback.lift_snd ..

instance finitePartialToOtherOrder_closed
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    IsClosedImmersion (finitePartialToOtherOrder k n S i hi) := by
  have : IsClosedImmersion (finitePartialToOtherOrder k n S i hi ≫
      pullback.snd (otherGlobalInclusion k n i) (componentTarget k n i)) := by
    rw [finitePartialToOtherOrder_snd]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.snd (otherGlobalInclusion k n i) (componentTarget k n i))

/-- Explicit symmetry matches the component-FIRST permanent full intersection. -/
def finitePartialToFull (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialIntersection k n S i ⟶ globalComponentComplement k n i :=
  finitePartialToOtherOrder k n S i hi ≫
    (pullbackSymmetry (otherGlobalInclusion k n i) (componentTarget k n i)).hom

@[reassoc (attr := simp)] lemma finitePartialToFull_first
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialToFull k n S i hi ≫ globalComplementFirst k n i =
      pullback.snd (unionMap (componentTarget k n) S) (componentTarget k n i) := by
  simp only [finitePartialToFull, globalComplementFirst, Category.assoc,
    pullbackSymmetry_hom_comp_fst, finitePartialToOtherOrder_snd]

@[reassoc (attr := simp)] lemma finitePartialToFull_second
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialToFull k n S i hi ≫ globalComplementSecond k n i =
      pullback.fst _ _ ≫ finiteUnionToOther k n S i hi := by
  simp only [finitePartialToFull, globalComplementSecond, Category.assoc,
    pullbackSymmetry_hom_comp_snd, finitePartialToOtherOrder_fst]

/-- Pullback symmetry preserves the actual closed partial-overlap map. -/
instance finitePartialToFull_closed (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    IsClosedImmersion (finitePartialToFull k n S i hi) := by
  unfold finitePartialToFull
  infer_instance

/-- Genuine closed-subscheme map into the already constructed split two-point scheme. -/
def finitePartialToTwoPoints (hn : 1 < n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialIntersection k n S i ⟶ Spec (.of (k × k)) :=
  finitePartialToFull k n S i hi ≫ (globalComponentComplementIsoTwoPoints k n hn i).hom

instance finitePartialToTwoPoints_closed
    (hn : 1 < n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    IsClosedImmersion (finitePartialToTwoPoints k n hn S i hi) := by
  unfold finitePartialToTwoPoints
  infer_instance

@[reassoc] lemma finitePartialToTwoPoints_over
    (hn : 1 < n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    finitePartialToTwoPoints k n hn S i hi ≫ Spec.algebraMap k (k × k) =
      pullback.snd (unionMap (componentTarget k n) S) (componentTarget k n i) ≫
        Scheme.PinchedLine.lineStructure k := by
  simp only [finitePartialToTwoPoints, Category.assoc,
    globalComponentComplementIsoTwoPoints_over, finitePartialToFull_first_assoc]

/-- All actual partial overlaps of the literal cyclic target are reduced.
The quotient algebra was already proved generically and is reused here. -/
theorem finitePartialIntersection_reduced
    (hn : 1 < n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    IsReduced (finitePartialIntersection k n S i) :=
  Scheme.TwoPoint.reduced_of_closed_into_twoPoints k
    (finitePartialToTwoPoints k n hn S i hi)

/-- Exact finite-descent hpartial telescope, now discharged for the cyclic target. -/
theorem targetPartialOverlap_family (hn : 1 < n) (S : Finset (Fin n)) :
    ∀ U : Finset (Fin n), U ⊆ S → ∀ i ∈ S, i ∉ U →
      IsReduced (pullback (unionMap (componentTarget k n) U) (componentTarget k n i)) := by
  intro U _ i _ hi
  exact finitePartialIntersection_reduced k n hn U i hi


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The same literal affine-coordinate point of the normalized projective line. -/
abbrev targetLinePoint (a : k) : Spec (.of k) ⟶ Scheme.PinchedLine.lineGluing k :=
  Scheme.PinchedLine.lineFieldPoint k a

/-- The canonical field point is literally the original affine branch followed by its chart. -/
lemma targetLinePoint_def (a : k) :
    targetLinePoint k a = Scheme.PinchedLine.branchMap k a ≫ selectedLineAffine k := rfl

@[reassoc] lemma selectedLineAffine_over :
    selectedLineAffine k ≫ Scheme.PinchedLine.lineStructure k = Spec.algebraMap k k[X] :=
  pushout.inl_desc ..

@[reassoc (attr := simp)] lemma targetLinePoint_over (a : k) :
    targetLinePoint k a ≫ Scheme.PinchedLine.lineStructure k = 𝟙 _ := by
  exact Scheme.PinchedLine.lineFieldPoint_structure k a

/-- The original-field point is a closed section of the same proper line. -/
instance targetLinePoint_closed (a : k) : IsClosedImmersion (targetLinePoint k a) :=
  isClosedImmersion_of_comp_eq_id (Scheme.PinchedLine.lineStructure k) (targetLinePoint k a)
    (targetLinePoint_over k a)

lemma targetLinePoint_apply (a : k) (z : Spec (.of k)) :
    targetLinePoint k a z = Scheme.PinchedLine.gluedBranchPoint k a := by
  change selectedLineAffine k (Scheme.PinchedLine.branchMap k a z) =
    selectedLineAffine k (Scheme.PinchedLine.branchPoint k a)
  congr 1
  apply Scheme.PinchedLine.branchPoint_eq_of_mem
  change Polynomial.eval a (X - C a) ∈ z.asIdeal
  simp

lemma endpointZero_boundary :
    endpointZeroSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) =
      Scheme.PinchedLine.branchMap k 0 := by
  unfold endpointZeroSection Scheme.PinchedLine.branchMap
  rw [← Spec.map_comp]
  congr 1

lemma endpointOne_boundary :
    endpointOneSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) =
      Scheme.PinchedLine.branchMap k 1 := by
  unfold endpointOneSection Scheme.PinchedLine.branchMap
  rw [← Spec.map_comp]
  congr 1

@[reassoc] lemma targetLinePoint_zero_node (i : Fin n) :
    targetLinePoint k 0 ≫ componentTarget k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n ((finRotate n).symm i))) ≫ cycleAffineChart k n
        := by
  calc
    _ = endpointZeroSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
        componentTargetAffine k n i ≫ cycleAffineChart k n := by
      rw [targetLinePoint_def, ← endpointZero_boundary]
      simp only [Category.assoc, componentTarget_affine]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ cycleAffineChart k n) (endpointZero_to_node k n i)

@[reassoc] lemma targetLinePoint_one_node (i : Fin n) :
    targetLinePoint k 1 ≫ componentTarget k n i =
      Spec.map (CommRingCat.ofHom (nodeValue k n i)) ≫ cycleAffineChart k n := by
  calc
    _ = endpointOneSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
        componentTargetAffine k n i ≫ cycleAffineChart k n := by
      rw [targetLinePoint_def, ← endpointOne_boundary]
      simp only [Category.assoc, componentTarget_affine]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ cycleAffineChart k n) (endpointOne_to_node k n i)

lemma target_endpoint_collision (i : Fin n) :
    targetLinePoint k 1 ≫ componentTarget k n i =
      targetLinePoint k 0 ≫ componentTarget k n (finRotate n i) := by
  rw [targetLinePoint_one_node, targetLinePoint_zero_node, Equiv.symm_apply_apply]

lemma componentTarget_branch_one (i : Fin n) :
    componentTarget k n i (Scheme.PinchedLine.gluedBranchPoint k 1) = gluedNodePoint k n i := by
  change gluedPolynomialCover k n (componentLine k n i (Scheme.PinchedLine.gluedBranchPoint k 1))
    = _
  rw [gluedBranch_on_component, gluedBranch_one_map]

lemma componentTarget_branch_zero (i : Fin n) :
    componentTarget k n i (Scheme.PinchedLine.gluedBranchPoint k 0) =
      gluedNodePoint k n ((finRotate n).symm i) := by
  change gluedPolynomialCover k n (componentLine k n i (Scheme.PinchedLine.gluedBranchPoint k 0))
    = _
  rw [gluedBranch_on_component]
  simpa only [Equiv.apply_symm_apply] using gluedBranch_zero_map k n ((finRotate n).symm i)

/-- A genuine pairwise intersection, with both original component projections. -/
abbrev targetPair (i j : Fin n) : Scheme.{u} := pullback (componentTarget k n i) (componentTarget
  k n j)

lemma targetPair_reduced (hn : 1 < n) (i j : Fin n) (hij : i ≠ j) :
    IsReduced (targetPair k n i j) := by
  let : ∀ a, IsClosedImmersion (componentTarget k n a) :=
    fun a => componentTarget_closedImmersion_of_one_lt k n hn a
  apply pair_reduced_of_singleton (componentTarget k n) j i
  exact finitePartialIntersection_reduced k n hn {i} j (by simpa using hij.symm)

/-- Exact node label of any actual pair point, derived from the original maps. -/
lemma targetPair_node_label (i j : Fin n) (hij : i ≠ j) (z : targetPair k n i j) :
    ∃ l, componentTarget k n i (pullback.fst (componentTarget k n i) (componentTarget k n j) z) =
      gluedNodePoint k n l ∧
      (i = l ∨ i = finRotate n l) ∧ (j = l ∨ j = finRotate n l) := by
  have hx : componentTarget k n i (pullback.fst (componentTarget k n i) (componentTarget k n j) z) ∈
      targetComponent k n i ∩ targetComponent k n j := by
    constructor
    · rw [← componentTarget_range]
      exact ⟨pullback.fst (componentTarget k n i) (componentTarget k n j) z, rfl⟩
    · rw [← componentTarget_range]
      refine ⟨pullback.snd (componentTarget k n i) (componentTarget k n j) z, ?_⟩
      exact (congrArg (fun f : targetPair k n i j ⟶ cycleScheme k n => f z)
        (pullback.condition (f := componentTarget k n i) (g := componentTarget k n j))).symm
  obtain ⟨l, hl⟩ := targetComponent_inter_subset_nodes k n i j hij hx
  rw [← hl] at hx
  exact ⟨l, hl.symm, (gluedNodePoint_on_component_iff k n l i).mp hx.1,
    (gluedNodePoint_on_component_iff k n l j).mp hx.2⟩

/-- Distinct non-neighbours have an actually empty scheme pullback. -/
lemma targetPair_empty_of_nonadjacent (i j : Fin n) (hij : i ≠ j)
    (hnext : j ≠ finRotate n i) (hprev : i ≠ finRotate n j) : IsEmpty (targetPair k n i j) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨l, _, hi, hj⟩ := targetPair_node_label k n i j hij z
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hij (hi.trans hj.symm)
  · exact hnext (hj.trans (congrArg (finRotate n) hi.symm))
  · exact hprev (hi.trans (congrArg (finRotate n) hj.symm))
  · exact hij (hi.trans hj.symm)

/-- The actual initial-scheme statement, not just an empty support label. -/
def targetPairInitialOfNonadjacent (i j : Fin n) (hij : i ≠ j)
    (hnext : j ≠ finRotate n i) (hprev : i ≠ finRotate n j) : IsInitial (targetPair k n i j) := by
  let := targetPair_empty_of_nonadjacent k n i j hij hnext hprev
  exact AlgebraicGeometry.isInitialOfIsEmpty


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

lemma rotate_twice_ne_self_of_two_lt (hn : 2 < n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro h
  have hadd : i + ((1 : Fin n) + 1) = i + 0 := by
    simpa only [finRotate_apply, add_assoc, add_zero] using h
  have htwo : (1 : Fin n) + 1 = 0 := add_left_cancel hadd
  have hv := congrArg Fin.val htwo
  have h1 : 1 < n := by omega
  simp only [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt h1] at hv
  norm_num only [Nat.reduceAdd] at hv
  rw [Nat.mod_eq_of_lt hn] at hv
  omega

/-- The canonical outgoing-one/incoming-zero pair point. -/
def outgoingPairPoint (i : Fin n) : Spec (.of k) ⟶ targetPair k n i (finRotate n i) :=
  pullback.lift (targetLinePoint k 1) (targetLinePoint k 0) (target_endpoint_collision k n i)

@[reassoc (attr := simp)] lemma outgoingPairPoint_fst (i : Fin n) :
    outgoingPairPoint k n i ≫ pullback.fst _ _ = targetLinePoint k 1 := pullback.lift_fst ..

@[reassoc (attr := simp)] lemma outgoingPairPoint_snd (i : Fin n) :
    outgoingPairPoint k n i ≫ pullback.snd _ _ = targetLinePoint k 0 := pullback.lift_snd ..

@[reassoc (attr := simp)] lemma outgoingPairPoint_over (i : Fin n) :
    outgoingPairPoint k n i ≫ pullback.fst _ _ ≫ Scheme.PinchedLine.lineStructure k = 𝟙 _ := by
  rw [outgoingPairPoint_fst_assoc, targetLinePoint_over]

/-- The exact outgoing pair point is a closed rational section. -/
instance outgoingPairPoint_closed (i : Fin n) : IsClosedImmersion (outgoingPairPoint k n i) :=
  isClosedImmersion_of_comp_eq_id (pullback.fst _ _ ≫ Scheme.PinchedLine.lineStructure k)
    (outgoingPairPoint k n i) (outgoingPairPoint_over k n i)

lemma adjacentPair_image (hn : 2 < n) (i : Fin n)
    (z : targetPair k n i (finRotate n i)) :
    componentTarget k n i (pullback.fst (componentTarget k n i) (componentTarget k n (finRotate n
      i)) z) = gluedNodePoint k n i := by
  have hn1 : 1 < n := by omega
  obtain ⟨l, hl, hi, hj⟩ := targetPair_node_label k n i (finRotate n i)
    (Fin.finRotate_ne_self_of_one_lt n hn1 i).symm z
  rcases hi with hi | hi
  · simpa only [← hi] using hl
  · rcases hj with hj | hj
    · exact (rotate_twice_ne_self_of_two_lt n hn l (by rw [← hi, hj])).elim
    · exact (Fin.finRotate_ne_self_of_one_lt n hn1 i (hj.trans hi.symm)).elim

lemma adjacentPair_first_endpoint (hn : 2 < n) (i : Fin n)
    (z : targetPair k n i (finRotate n i)) :
    pullback.fst (componentTarget k n i) (componentTarget k n (finRotate n i)) z =
      Scheme.PinchedLine.gluedBranchPoint k 1 := by
  have hp := adjacentPair_image k n hn i z
  have hx : componentTarget k n i (pullback.fst (componentTarget k n i) (componentTarget k n
    (finRotate n i)) z) ∈ globalNodeLocus k n :=
    ⟨i, hp.symm⟩
  rcases componentLine_node_preimage k n i (pullback.fst (componentTarget k n i) (componentTarget
    k n (finRotate n i)) z) hx with h0 | h1
  · rw [h0, componentTarget_branch_zero] at hp
    exact (Fin.finRotate_symm_ne_self_of_one_lt n (by omega) i (gluedNodePoint_injective k n
      hp)).elim
  · exact h1

lemma outgoingPairPoint_surjective (hn : 2 < n) (i : Fin n) :
    Surjective (outgoingPairPoint k n i) := by
  let : IsClosedImmersion (componentTarget k n (finRotate n i)) :=
    componentTarget_closedImmersion_of_one_lt k n (by omega) _
  constructor
  intro z
  refine ⟨IsLocalRing.closedPoint k, ?_⟩
  apply (pullback.fst (componentTarget k n i) (componentTarget k n (finRotate n
    i))).isClosedEmbedding.injective
  calc
    _ = targetLinePoint k 1 (IsLocalRing.closedPoint k) :=
      congrArg (fun f => f (IsLocalRing.closedPoint k)) (outgoingPairPoint_fst k n i)
    _ = Scheme.PinchedLine.gluedBranchPoint k 1 := targetLinePoint_apply k 1 _
    _ = _ := (adjacentPair_first_endpoint k n hn i z).symm

/-- Scheme-level result: closed + surjective onto the genuinely reduced pair. -/
lemma outgoingPairPoint_isIso (hn : 2 < n) (i : Fin n) : IsIso (outgoingPairPoint k n i) := by
  let := targetPair_reduced k n (by omega) i (finRotate n i)
    (Fin.finRotate_ne_self_of_one_lt n (by omega) i).symm
  let := outgoingPairPoint_surjective k n hn i
  exact isIso_of_isClosedImmersion_of_surjective (outgoingPairPoint k n i)

/-- The actual neighboring-component intersection for levels greater than two. -/
def outgoingPairIso (hn : 2 < n) (i : Fin n) :
    targetPair k n i (finRotate n i) ≅ Spec (.of k) := by
  let := outgoingPairPoint_isIso k n hn i
  exact (asIso (outgoingPairPoint k n i)).symm

@[reassoc (attr := simp)] lemma outgoingPairIso_inv_fst (hn : 2 < n) (i : Fin n) :
    (outgoingPairIso k n hn i).inv ≫ pullback.fst _ _ = targetLinePoint k 1 :=
  outgoingPairPoint_fst k n i

@[reassoc (attr := simp)] lemma outgoingPairIso_inv_snd (hn : 2 < n) (i : Fin n) :
    (outgoingPairIso k n hn i).inv ≫ pullback.snd _ _ = targetLinePoint k 0 :=
  outgoingPairPoint_snd k n i

@[reassoc] lemma outgoingPairIso_over (hn : 2 < n) (i : Fin n) :
    (outgoingPairIso k n hn i).hom =
      pullback.fst (componentTarget k n i) (componentTarget k n (finRotate n i)) ≫
        Scheme.PinchedLine.lineStructure k := by
  rw [← cancel_epi (outgoingPairIso k n hn i).inv]
  simp

/-- Actual cartesian endpoint square, with no cartesianness premise. -/
lemma outgoingPair_isPullback (hn : 2 < n) (i : Fin n) :
    IsPullback (targetLinePoint k 1) (targetLinePoint k 0)
      (componentTarget k n i) (componentTarget k n (finRotate n i)) :=
  IsPullback.of_iso_pullback ⟨target_endpoint_collision k n i⟩
    (outgoingPairIso k n hn i).symm
    (outgoingPairIso_inv_fst k n hn i) (outgoingPairIso_inv_snd k n hn i)

/-- Reverse ordering retains the corresponding swapped original projections. -/
def reverseOutgoingPairIso (hn : 2 < n) (i : Fin n) :
    targetPair k n (finRotate n i) i ≅ Spec (.of k) :=
  pullbackSymmetry (componentTarget k n (finRotate n i)) (componentTarget k n i) ≪≫
    outgoingPairIso k n hn i

@[reassoc (attr := simp)] lemma reverseOutgoingPairIso_inv_fst (hn : 2 < n) (i : Fin n) :
    (reverseOutgoingPairIso k n hn i).inv ≫ pullback.fst _ _ = targetLinePoint k 0 := by
  simp [reverseOutgoingPairIso]

@[reassoc (attr := simp)] lemma reverseOutgoingPairIso_inv_snd (hn : 2 < n) (i : Fin n) :
    (reverseOutgoingPairIso k n hn i).inv ≫ pullback.snd _ _ = targetLinePoint k 1 := by
  simp [reverseOutgoingPairIso]


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k]

lemma rotate_two_eq_other (i j : Fin 2) (hij : i ≠ j) : finRotate 2 i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [finRotate_apply]

/-- In the actual two-cycle, the full complement is exactly the OTHER component ideal. -/
lemma otherGlobalIdeal_two_eq_component (i j : Fin 2) (hij : i ≠ j) :
    otherGlobalIdeal k 2 i = (componentTarget k 2 j).ker := by
  rw [otherGlobalIdeal_eq_iInf]
  apply le_antisymm
  · exact iInf_le (fun a : {a : Fin 2 // a ≠ i} => (componentTarget k 2 a.val).ker) ⟨j, hij.symm⟩
  · apply le_iInf
    intro a
    have ha : a.val = j := by
      apply Fin.ext
      have h₁ : a.val.val ≠ i.val := fun h => a.property (Fin.ext h)
      have h₂ : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have := a.val.isLt
      have := i.isLt
      have := j.isLt
      omega
    rw [ha]

/-- The original other component factors through that exact native complement. -/
def twoOtherFactor (i j : Fin 2) (hij : i ≠ j) :
    Scheme.PinchedLine.lineGluing k ⟶ otherGlobalScheme k 2 i :=
  IsClosedImmersion.lift (otherGlobalInclusion k 2 i) (componentTarget k 2 j) (by
    rw [ker_subschemeι, otherGlobalIdeal_two_eq_component k i j hij])

@[reassoc (attr := simp)] lemma twoOtherFactor_triangle (i j : Fin 2) (hij : i ≠ j) :
    twoOtherFactor k i j hij ≫ otherGlobalInclusion k 2 i = componentTarget k 2 j :=
  IsClosedImmersion.lift_fac ..

/-- The other actual two-cycle component is exactly the full complement scheme. -/
instance twoOtherFactor_isIso (i j : Fin 2) (hij : i ≠ j) : IsIso (twoOtherFactor k i j hij) := by
  let := componentTarget_closedImmersion_of_one_lt k 2 (by decide) j
  exact IsClosedImmersion.isIso_of_ker_eq (componentTarget k 2 j) (otherGlobalInclusion k 2 i)
    (twoOtherFactor k i j hij) (twoOtherFactor_triangle k i j hij)
    (by rw [ker_subschemeι, otherGlobalIdeal_two_eq_component k i j hij])

/-- The original ordered two-component pair mapped into its exact full complement. -/
def twoPairToFull (i j : Fin 2) (hij : i ≠ j) :
    targetPair k 2 i j ⟶ globalComponentComplement k 2 i :=
  pullback.map (componentTarget k 2 i) (componentTarget k 2 j)
    (componentTarget k 2 i) (otherGlobalInclusion k 2 i)
    (𝟙 _) (twoOtherFactor k i j hij) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)] lemma twoPairToFull_fst (i j : Fin 2) (hij : i ≠ j) :
    twoPairToFull k i j hij ≫ globalComplementFirst k 2 i = pullback.fst _ _ := by
  unfold twoPairToFull globalComplementFirst pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)] lemma twoPairToFull_snd (i j : Fin 2) (hij : i ≠ j) :
    twoPairToFull k i j hij ≫ globalComplementSecond k 2 i =
      pullback.snd _ _ ≫ twoOtherFactor k i j hij := by
  unfold twoPairToFull globalComplementSecond pullback.map
  exact pullback.lift_snd _ _ _

/-- The actual two-cycle pair comparison is an isomorphism by base change. -/
instance twoPairToFull_isIso (i j : Fin 2) (hij : i ≠ j) : IsIso (twoPairToFull k i j hij) := by
  unfold twoPairToFull
  infer_instance

/-- Actual scheme-theoretic two-point intersection of the two original components. -/
def twoPairIso (i j : Fin 2) (hij : i ≠ j) : targetPair k 2 i j ≅ Spec (.of (k × k)) :=
  asIso (twoPairToFull k i j hij) ≪≫ globalComponentComplementIsoTwoPoints k 2 (by decide) i

/-- The original two boundary points mapped into the same normalized line. -/
def boundaryLineMap : Spec (.of (k × k)) ⟶ Scheme.PinchedLine.lineGluing k :=
  Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫ selectedLineAffine k

@[reassoc] lemma twoPairIso_hom_boundary (i j : Fin 2) (hij : i ≠ j) :
    (twoPairIso k i j hij).hom ≫ boundaryLineMap k = pullback.fst _ _ := by
  simp only [twoPairIso, Iso.trans_hom, asIso_hom, boundaryLineMap, Category.assoc,
    globalComponentComplementIsoTwoPoints_endpoints, twoPairToFull_fst]

@[reassoc (attr := simp)] lemma twoPairIso_inv_fst (i j : Fin 2) (hij : i ≠ j) :
    (twoPairIso k i j hij).inv ≫ pullback.fst _ _ = boundaryLineMap k := by
  rw [← cancel_epi (twoPairIso k i j hij).hom]
  simp only [Iso.hom_inv_id_assoc, twoPairIso_hom_boundary]

@[reassoc] lemma twoPairIso_over (i j : Fin 2) (hij : i ≠ j) :
    (twoPairIso k i j hij).hom ≫ Spec.algebraMap k (k × k) =
      pullback.fst (componentTarget k 2 i) (componentTarget k 2 j) ≫
        Scheme.PinchedLine.lineStructure k := by
  simp only [twoPairIso, Iso.trans_hom, asIso_hom, Category.assoc,
    globalComponentComplementIsoTwoPoints_over, twoPairToFull_fst_assoc]

/-- Existing Spec-product/coproduct iso explicitly orders the two original endpoints. -/
lemma boundaryLineMap_coprod :
    boundaryLineMap k = (Scheme.Pullback.SpecProducts.specProductIso k k).hom ≫
      coprod.desc (targetLinePoint k 0) (targetLinePoint k 1) := by
  rw [← cancel_epi (Scheme.Pullback.SpecProducts.specProductIso k k).inv]
  apply coprod.hom_ext
  · simp only [Iso.inv_hom_id_assoc, coprod.inl_desc,
      Scheme.Pullback.SpecProducts.specProductIso_inl_assoc]
    change endpointZeroSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
      selectedLineAffine k = targetLinePoint k 0
    rw [← Category.assoc, endpointZero_boundary]
    rfl
  · simp only [Iso.inv_hom_id_assoc, coprod.inr_desc,
      Scheme.Pullback.SpecProducts.specProductIso_inr_assoc]
    change endpointOneSection k ≫ Spec.map (CommRingCat.ofHom (baseBoundary k).toRingHom) ≫
      selectedLineAffine k = targetLinePoint k 1
    rw [← Category.assoc, endpointOne_boundary]
    rfl

/-- On the OTHER component the endpoint order is reversed, not identified. -/
def reverseBoundaryLineMap : Spec (.of (k × k)) ⟶ Scheme.PinchedLine.lineGluing k :=
  (Scheme.Pullback.SpecProducts.specProductIso k k).hom ≫
    coprod.desc (targetLinePoint k 1) (targetLinePoint k 0)

/-- The incoming point has zero on the first component and one on the second. -/
def twoIncomingPoint (i j : Fin 2) (hij : i ≠ j) : Spec (.of k) ⟶ targetPair k 2 i j :=
  pullback.lift (targetLinePoint k 0) (targetLinePoint k 1) (by
    simpa only [rotate_two_eq_other j i hij.symm] using (target_endpoint_collision k 2 j).symm)

/-- The outgoing point has one on the first component and zero on the second. -/
def twoOutgoingPoint (i j : Fin 2) (hij : i ≠ j) : Spec (.of k) ⟶ targetPair k 2 i j :=
  pullback.lift (targetLinePoint k 1) (targetLinePoint k 0) (by
    simpa only [rotate_two_eq_other i j hij] using target_endpoint_collision k 2 i)

@[reassoc (attr := simp)] lemma twoIncomingPoint_fst (i j : Fin 2) (hij : i ≠ j) :
    twoIncomingPoint k i j hij ≫ pullback.fst _ _ = targetLinePoint k 0 := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma twoIncomingPoint_snd (i j : Fin 2) (hij : i ≠ j) :
    twoIncomingPoint k i j hij ≫ pullback.snd _ _ = targetLinePoint k 1 := pullback.lift_snd ..
@[reassoc (attr := simp)] lemma twoOutgoingPoint_fst (i j : Fin 2) (hij : i ≠ j) :
    twoOutgoingPoint k i j hij ≫ pullback.fst _ _ = targetLinePoint k 1 := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma twoOutgoingPoint_snd (i j : Fin 2) (hij : i ≠ j) :
    twoOutgoingPoint k i j hij ≫ pullback.snd _ _ = targetLinePoint k 0 := pullback.lift_snd ..

/-- The actual two pair points assembled in the canonical original order. -/
def canonicalTwoPairMap (i j : Fin 2) (hij : i ≠ j) : Spec (.of (k × k)) ⟶ targetPair k 2 i j :=
  (Scheme.Pullback.SpecProducts.specProductIso k k).hom ≫
    coprod.desc (twoIncomingPoint k i j hij) (twoOutgoingPoint k i j hij)

@[reassoc (attr := simp)] lemma canonicalTwoPairMap_fst (i j : Fin 2) (hij : i ≠ j) :
    canonicalTwoPairMap k i j hij ≫ pullback.fst _ _ = boundaryLineMap k := by
  rw [boundaryLineMap_coprod]
  simp [canonicalTwoPairMap, Category.assoc, coprod.desc_comp]

@[reassoc (attr := simp)] lemma canonicalTwoPairMap_snd (i j : Fin 2) (hij : i ≠ j) :
    canonicalTwoPairMap k i j hij ≫ pullback.snd _ _ = reverseBoundaryLineMap k := by
  simp [canonicalTwoPairMap, reverseBoundaryLineMap, Category.assoc, coprod.desc_comp]

lemma twoPairIso_inv_eq_canonical (i j : Fin 2) (hij : i ≠ j) :
    (twoPairIso k i j hij).inv = canonicalTwoPairMap k i j hij := by
  let := componentTarget_closedImmersion_of_one_lt k 2 (by decide) j
  rw [← cancel_mono (pullback.fst (componentTarget k 2 i) (componentTarget k 2 j))]
  rw [twoPairIso_inv_fst, canonicalTwoPairMap_fst]

/-- Both inverse projections are explicit; the second retains swapped endpoints. -/
@[reassoc (attr := simp)] lemma twoPairIso_inv_snd (i j : Fin 2) (hij : i ≠ j) :
    (twoPairIso k i j hij).inv ≫ pullback.snd _ _ = reverseBoundaryLineMap k := by
  rw [twoPairIso_inv_eq_canonical, canonicalTwoPairMap_snd]

lemma twoPair_isPullback (i j : Fin 2) (hij : i ≠ j) :
    IsPullback (boundaryLineMap k) (reverseBoundaryLineMap k)
      (componentTarget k 2 i) (componentTarget k 2 j) := by
  apply IsPullback.of_iso_pullback _ (twoPairIso k i j hij).symm
    (twoPairIso_inv_fst k i j hij) (twoPairIso_inv_snd k i j hij)
  constructor
  rw [← twoPairIso_inv_fst k i j hij, ← twoPairIso_inv_snd k i j hij]
  simp only [Category.assoc, pullback.condition]


end AlgebraicGeometry.Scheme.Polygon
