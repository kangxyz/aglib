/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.ReducedClosedUnion
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme

/-!
# Finite reduced closed unions and descent

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.FiniteClosedCover`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `abe641ae5a82c0be4abb602bea9a380685f49d63f67c2dc2e106bb944633b94d`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v


section

/-! Canonical finite reduced closed unions and their actual maps.
Every scheme is an actual ideal subscheme. No distribution of intersections
through pullback is assumed. -/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.FiniteClosedCover
open Scheme.IdealSheafData
variable {ι : Type v} [DecidableEq ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
  (i : ∀ a, Y a ⟶ X) [∀ a, IsClosedImmersion (i a)] [∀ a, IsReduced (Y a)]

def unionIdeal (S : Finset ι) : X.IdealSheafData :=
  ⨅ a : {a : ι // a ∈ S}, (i a.val).ker
abbrev unionScheme (S : Finset ι) : Scheme.{u} := (unionIdeal i S).subscheme
abbrev unionMap (S : Finset ι) : unionScheme i S ⟶ X := (unionIdeal i S).subschemeι

omit [DecidableEq ι] in
lemma unionIdeal_radical (S : Finset ι) : (unionIdeal i S).radical = unionIdeal i S := by
  classical
  ext U : 2
  change ((unionIdeal i S).ideal U).radical = (unionIdeal i S).ideal U
  simp only [unionIdeal, ideal_iInf, iInf_apply]
  apply Ideal.radical_eq_iff.mpr
  apply Ideal.isRadical_iInf
  intro a
  apply Ideal.radical_eq_iff.mp
  exact congrArg (fun J : X.IdealSheafData => J.ideal U)
    (Scheme.IdealSheafData.kernel_radical (i a.val))

omit [DecidableEq ι] in
instance unionScheme_reduced (S : Finset ι) : IsReduced (unionScheme i S) :=
  Scheme.IdealSheafData.subscheme_reduced_of_radical _ (unionIdeal_radical i S)

/-- Literal finite union of the original component images. -/
def unionSupport (S : Finset ι) : TopologicalSpace.Closeds X :=
  ⟨⋃ a : {a : ι // a ∈ S}, Set.range (i a.val),
    isClosed_iUnion_of_finite (fun a => (i a.val).isClosedEmbedding.isClosed_range)⟩

omit [DecidableEq ι] in
lemma unionIdeal_eq_vanishingIdeal (S : Finset ι) :
    unionIdeal i S = vanishingIdeal (unionSupport i S) := by
  classical
  have hs : unionSupport i S =
      ⨆ a : {a : ι // a ∈ S},
        (⟨Set.range (i a.val), (i a.val).isClosedEmbedding.isClosed_range⟩ :
          TopologicalSpace.Closeds X) := by
    apply le_antisymm
    · rintro x hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact le_iSup (fun a : {a : ι // a ∈ S} =>
        (⟨Set.range (i a.val), (i a.val).isClosedEmbedding.isClosed_range⟩ :
          TopologicalSpace.Closeds X)) a ha
    · apply iSup_le
      intro a x hx
      exact Set.mem_iUnion.mpr ⟨a, hx⟩
  rw [hs, vanishingIdeal_iSup]
  unfold unionIdeal
  congr 1
  funext a
  rw [Scheme.IdealSheafData.kernel_eq_vanishingIdeal]
  congr 1
  ext x
  simp only [Scheme.Hom.support_ker]
  change x ∈ closure (Set.range (i a.val)) ↔ x ∈ Set.range (i a.val)
  rw [(i a.val).isClosedEmbedding.isClosed_range.closure_eq]

omit [DecidableEq ι] in
lemma unionMap_range (S : Finset ι) :
    Set.range (unionMap i S) = ⋃ a : {a : ι // a ∈ S}, Set.range (i a.val) := by
  rw [range_subschemeι, unionIdeal_eq_vanishingIdeal]
  exact coe_support_vanishingIdeal _

omit [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)] in
omit [DecidableEq ι] in
@[simp] lemma unionIdeal_empty
    [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)]
    : unionIdeal i ∅ = ⊤ := by
  classical
  simp [unionIdeal]

omit [DecidableEq ι] in
instance unionScheme_empty : IsEmpty (unionScheme i ∅) := by
  change IsEmpty (unionIdeal i ∅).subscheme
  rw [unionIdeal_empty]
  infer_instance

def emptyUnionIsInitial : IsInitial (unionScheme i ∅) := AlgebraicGeometry.isInitialOfIsEmpty

omit [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)] in
omit [DecidableEq ι] in
lemma unionIdeal_antitone
    [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)]
    {S T : Finset ι} (h : S ⊆ T) : unionIdeal i T ≤ unionIdeal i S := by
  apply le_iInf
  intro a
  exact iInf_le_of_le ⟨a.val, h a.property⟩ le_rfl

def unionInclusion {S T : Finset ι} (h : S ⊆ T) : unionScheme i S ⟶ unionScheme i T :=
  Scheme.IdealSheafData.inclusion (unionIdeal_antitone i h)

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma unionInclusion_triangle {S T : Finset ι} (h : S ⊆ T) :
    unionInclusion i h ≫ unionMap i T = unionMap i S := inclusion_subschemeι _

omit [DecidableEq ι] in
instance unionInclusion_closed {S T : Finset ι} (h : S ⊆ T) :
    IsClosedImmersion (unionInclusion i h) := by
  have : IsClosedImmersion (unionInclusion i h ≫ unionMap i T) := by
    rw [unionInclusion_triangle]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (unionMap i T)

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma unionInclusion_comp
    {S T U : Finset ι} (hST : S ⊆ T) (hTU : T ⊆ U) :
    unionInclusion i hST ≫ unionInclusion i hTU = unionInclusion i (hST.trans hTU) := by
  rw [← cancel_mono (unionMap i U)]
  simp

omit [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)] in
omit [DecidableEq ι] in
lemma unionIdeal_le_component
    [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsReduced (Y a)]
    (S : Finset ι) (a : ι) (ha : a ∈ S) :
    unionIdeal i S ≤ (i a).ker := by
  unfold unionIdeal
  exact iInf_le (fun b : {b : ι // b ∈ S} => (i b.val).ker) ⟨a, ha⟩

/-- Factor of the original closed component map through its actual finite union. -/
def componentToUnion (S : Finset ι) (a : ι) (ha : a ∈ S) : Y a ⟶ unionScheme i S :=
  IsClosedImmersion.lift (unionMap i S) (i a) (by
    rw [ker_subschemeι]
    exact unionIdeal_le_component i S a ha)

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma componentToUnion_triangle
    (S : Finset ι) (a : ι) (ha : a ∈ S) :
    componentToUnion i S a ha ≫ unionMap i S = i a := IsClosedImmersion.lift_fac ..

omit [DecidableEq ι] in
instance componentToUnion_closed (S : Finset ι) (a : ι) (ha : a ∈ S) :
    IsClosedImmersion (componentToUnion i S a ha) := by
  have : IsClosedImmersion (componentToUnion i S a ha ≫ unionMap i S) := by
    rw [componentToUnion_triangle]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (unionMap i S)

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma componentToUnion_naturality
    {S T : Finset ι} (h : S ⊆ T) (a : ι) (ha : a ∈ S) :
    componentToUnion i S a ha ≫ unionInclusion i h = componentToUnion i T a (h ha) := by
  rw [← cancel_mono (unionMap i T)]
  simp

omit [DecidableEq ι] in
lemma unionIdeal_singleton (a : ι) : unionIdeal i {a} = (i a).ker := by
  classical
  apply le_antisymm
  · exact unionIdeal_le_component i {a} a (by simp)
  · apply le_iInf
    intro b
    have hb : b.val = a := Finset.mem_singleton.mp b.property
    rw [hb]

omit [DecidableEq ι] in
instance singleton_componentToUnion_isIso (a : ι) :
    IsIso (componentToUnion i {a} a (Finset.mem_singleton_self a)) := by
  classical
  exact IsClosedImmersion.isIso_of_ker_eq (i a) (unionMap i {a})
    (componentToUnion i {a} a (Finset.mem_singleton_self a))
    (componentToUnion_triangle i {a} a (Finset.mem_singleton_self a))
    (by rw [ker_subschemeι, unionIdeal_singleton])

/-- Actual singleton union isomorphism, with the original component map. -/
def singletonIso (a : ι) : Y a ≅ unionScheme i {a} :=
  asIso (componentToUnion i {a} a (Finset.mem_singleton_self a))

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma singletonIso_hom_triangle (a : ι) :
    (singletonIso i a).hom ≫ unionMap i {a} = i a :=
  componentToUnion_triangle i {a} a (Finset.mem_singleton_self a)

omit [DecidableEq ι] in
@[reassoc (attr := simp)] lemma singletonIso_inv_triangle (a : ι) :
    (singletonIso i a).inv ≫ i a = unionMap i {a} := by
  rw [← singletonIso_hom_triangle i a, Iso.inv_hom_id_assoc]

omit [DecidableEq ι] in
/-- Every point of the actual finite union is in an actual component factor. -/
lemma componentToUnion_ranges_cover (S : Finset ι) :
    (⋃ a : {a : ι // a ∈ S}, Set.range (componentToUnion i S a.val a.property)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : unionMap i S x ∈ Set.range (unionMap i S) := ⟨x, rfl⟩
  rw [unionMap_range] at hx
  obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨a, y, (unionMap i S).isClosedEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, componentToUnion_triangle] using hy

/-- Binary coverage inside the actual inserted union; not an assumed certificate. -/
lemma insert_ranges_cover (S : Finset ι) (a : ι) :
    Set.range (unionInclusion i (Finset.subset_insert a S)) ∪
      Set.range (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hx : unionMap i (insert a S) x ∈ Set.range (unionMap i (insert a S)) := ⟨x, rfl⟩
  rw [unionMap_range] at hx
  obtain ⟨⟨b, hbS⟩, y, hy⟩ := Set.mem_iUnion.mp hx
  rcases Finset.mem_insert.mp hbS with rfl | hb
  · right
    refine ⟨y, (unionMap i (insert b S)).isClosedEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, componentToUnion_triangle] using hy
  · left
    refine ⟨componentToUnion i S b hb y,
      (unionMap i (insert a S)).isClosedEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, unionInclusion_triangle,
      componentToUnion_triangle, Category.assoc] using hy

omit [DecidableEq ι] in
lemma fullUnionMap_isIso [IsReduced X] (S : Finset ι)
    (hcover : (⋃ a : {a : ι // a ∈ S}, Set.range (i a.val)) = Set.univ) :
    IsIso (unionMap i S) := by
  have : Surjective (unionMap i S) := ⟨by
    rw [← Set.range_eq_univ, unionMap_range]
    exact hcover⟩
  exact isIso_of_isClosedImmersion_of_surjective (unionMap i S)

def fullUnionIso [IsReduced X] (S : Finset ι)
    (hcover : (⋃ a : {a : ι // a ∈ S}, Set.range (i a.val)) = Set.univ) :
    unionScheme i S ≅ X := by
  let := fullUnionMap_isIso i S hcover
  exact asIso (unionMap i S)

end AlgebraicGeometry.Scheme.FiniteClosedCover

end -- noncomputable section
end


/-! Finite joint uniqueness is derived
from actual ideal unions and the binary closed-cover theorem; no separatedness
of the target is assumed. -/
namespace AlgebraicGeometry.Scheme.FiniteClosedCover

variable {ι : Type v} [DecidableEq ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
  (i : ∀ a, Y a ⟶ X) [∀ a, IsClosedImmersion (i a)] [∀ a, IsReduced (Y a)]

omit [DecidableEq ι] in
/-- The actual component factors are jointly faithful on an actual finite union. -/
theorem union_hom_ext (S : Finset ι) {T : Scheme.{u}}
    {f g : unionScheme i S ⟶ T}
    (h : ∀ a (ha : a ∈ S), componentToUnion i S a ha ≫ f =
      componentToUnion i S a ha ≫ g) : f = g := by
  classical
  revert f g
  induction S using Finset.induction_on with
  | empty =>
      intro f g h
      exact (emptyUnionIsInitial i).hom_ext f g
  | @insert a S ha ih =>
      intro f g h
      apply ReducedClosedUnion.hom_ext
        (unionInclusion i (Finset.subset_insert a S))
        (componentToUnion i (insert a S) a (Finset.mem_insert_self a S))
        (insert_ranges_cover i S a)
      · apply ih
        intro b hb
        simpa only [← Category.assoc, componentToUnion_naturality] using
          h b (Finset.mem_insert_of_mem hb)
      · exact h a (Finset.mem_insert_self a S)

omit [DecidableEq ι] in
/-- Joint uniqueness for finitely many actual reduced closed subschemes
covering a reduced ambient scheme. All maps are the original component maps. -/
theorem hom_ext [IsReduced X] (S : Finset ι)
    (hcover : (⋃ a : {a : ι // a ∈ S}, Set.range (i a.val)) = Set.univ)
    {T : Scheme.{u}} {f g : X ⟶ T}
    (h : ∀ a ∈ S, i a ≫ f = i a ≫ g) : f = g := by
  let := fullUnionMap_isIso i S hcover
  apply (cancel_epi (unionMap i S)).mp
  apply union_hom_ext i S
  intro a ha
  simpa only [← Category.assoc, componentToUnion_triangle] using h a ha

omit [DecidableEq ι] in
/-- Finite-index version, useful for the actual pairwise closed cover of an
actual partial-union overlap. -/
theorem hom_ext_finite [Finite ι] [IsReduced X]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    {T : Scheme.{u}} {f g : X ⟶ T}
    (h : ∀ a, i a ≫ f = i a ≫ g) : f = g := by
  classical
  let := Fintype.ofFinite ι
  apply hom_ext i Finset.univ
  · simpa only [Set.iUnion_subtype, Finset.mem_univ, Set.iUnion_true] using hcover
  · intro a ha
    exact h a

end AlgebraicGeometry.Scheme.FiniteClosedCover

section

/-! The actual pairwise pullbacks cover
the actual partial-union pullback. No ideal-inf/pullback distribution is used. -/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteClosedCover

variable {ι : Type v} [DecidableEq ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
  (i : ∀ a, Y a ⟶ X) [∀ a, IsClosedImmersion (i a)] [∀ a, IsReduced (Y a)]

/-- Map from a genuine pairwise intersection into the genuine partial overlap. -/
def pairToOverlap (S : Finset ι) (a b : ι) (hb : b ∈ S) :
    pullback (i b) (i a) ⟶ pullback (unionMap i S) (i a) :=
  pullback.map (i b) (i a) (unionMap i S) (i a)
    (componentToUnion i S b hb) (𝟙 _) (𝟙 _) (by simp) (by simp)

omit [DecidableEq ι] in
@[reassoc (attr := simp)]
lemma pairToOverlap_fst (S : Finset ι) (a b : ι) (hb : b ∈ S) :
    pairToOverlap i S a b hb ≫ pullback.fst (unionMap i S) (i a) =
      pullback.fst (i b) (i a) ≫ componentToUnion i S b hb := by
  unfold pairToOverlap pullback.map
  exact pullback.lift_fst _ _ _

omit [DecidableEq ι] in
@[reassoc (attr := simp)]
lemma pairToOverlap_snd (S : Finset ι) (a b : ι) (hb : b ∈ S) :
    pairToOverlap i S a b hb ≫ pullback.snd (unionMap i S) (i a) =
      pullback.snd (i b) (i a) := by
  unfold pairToOverlap pullback.map
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [DecidableEq ι] in
instance pairToOverlap_closed (S : Finset ι) (a b : ι) (hb : b ∈ S) :
    IsClosedImmersion (pairToOverlap i S a b hb) := by
  have : IsClosedImmersion
      (pairToOverlap i S a b hb ≫ pullback.snd (unionMap i S) (i a)) := by
    rw [pairToOverlap_snd]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.snd (unionMap i S) (i a))

omit [DecidableEq ι] in
/-- Topological coverage proved for the actual maps, not supplied as a certificate. -/
lemma pairToOverlap_ranges_cover (S : Finset ι) (a : ι) :
    (⋃ b : {b : ι // b ∈ S}, Set.range (pairToOverlap i S a b.val b.property)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  have hw : pullback.fst (unionMap i S) (i a) w ∈
      ⋃ b : {b : ι // b ∈ S}, Set.range (componentToUnion i S b.val b.property) := by
    rw [componentToUnion_ranges_cover]
    trivial
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hw
  apply Set.mem_iUnion.mpr
  refine ⟨b, ?_⟩
  rw [pairToOverlap, Scheme.Pullback.range_map]
  exact ⟨hb, ⟨pullback.snd (unionMap i S) (i a) w, by simp⟩⟩

omit [DecidableEq ι] in
instance pairToSingletonOverlap_isIso (a b : ι) :
    IsIso (pairToOverlap i {b} a b (Finset.mem_singleton_self b)) := by
  unfold pairToOverlap
  infer_instance

/-- Singleton transport retains both actual projections by the preceding lemmas. -/
def pairSingletonIso (a b : ι) :
    pullback (i b) (i a) ≅ pullback (unionMap i {b}) (i a) :=
  asIso (pairToOverlap i {b} a b (Finset.mem_singleton_self b))

omit [DecidableEq ι] in
lemma pair_reduced_of_singleton (a b : ι)
    (h : IsReduced (pullback (unionMap i {b}) (i a))) :
    IsReduced (pullback (i b) (i a)) := by
  let := h
  exact isReduced_of_isOpenImmersion (pairSingletonIso i a b).hom

omit [DecidableEq ι] in
/-- Joint uniqueness on a reduced actual partial overlap, using its actual
pairwise closed cover. Reducedness is explicit rather than inferred from
reducedness of the ambient components. -/
theorem partialOverlap_hom_ext (S : Finset ι) (a : ι)
    [IsReduced (pullback (unionMap i S) (i a))]
    [∀ b : {b : ι // b ∈ S}, IsReduced (pullback (i b.val) (i a))]
    {T : Scheme.{u}} {f g : pullback (unionMap i S) (i a) ⟶ T}
    (h : ∀ b (hb : b ∈ S), pairToOverlap i S a b hb ≫ f =
      pairToOverlap i S a b hb ≫ g) : f = g := by
  apply hom_ext_finite (fun b : {b : ι // b ∈ S} =>
    pairToOverlap i S a b.val b.property) (pairToOverlap_ranges_cover i S a)
  intro b
  exact h b.val b.property

/-- Comparison from the binary-step intersection to the ambient intersection.
No reducedness assertion is needed for its source. -/
def insertOverlapToAmbient (S : Finset ι) (a : ι) :
    pullback (unionInclusion i (Finset.subset_insert a S))
      (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) ⟶
        pullback (unionMap i S) (i a) :=
  pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (unionMap i (insert a S)) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma insertOverlapToAmbient_fst (S : Finset ι) (a : ι) :
    insertOverlapToAmbient i S a ≫ pullback.fst (unionMap i S) (i a) =
      pullback.fst (unionInclusion i (Finset.subset_insert a S))
        (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) := by
  unfold insertOverlapToAmbient pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma insertOverlapToAmbient_snd (S : Finset ι) (a : ι) :
    insertOverlapToAmbient i S a ≫ pullback.snd (unionMap i S) (i a) =
      pullback.snd (unionInclusion i (Finset.subset_insert a S))
        (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) := by
  unfold insertOverlapToAmbient pullback.map
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end AlgebraicGeometry.Scheme.FiniteClosedCover

end -- original EOF scope

end


section

/-! Finite descent follows by genuine
binary Scheme pushouts. The necessary reducedness of actual partial overlaps
is displayed explicitly, and is not replaced by pairwise reducedness. -/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteClosedCover

variable {ι : Type v} [DecidableEq ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
  (i : ∀ a, Y a ⟶ X) [∀ a, IsClosedImmersion (i a)] [∀ a, IsReduced (Y a)]

omit [DecidableEq ι] in
/-- Compatible maps descend to the actual finite union. Only partial overlaps
inside this finite set are required to be reduced. -/
theorem exists_union_desc (S : Finset ι)
    (hpartial : ∀ U : Finset ι, U ⊆ S → ∀ a ∈ S, a ∉ U →
      IsReduced (pullback (unionMap i U) (i a)))
    {T : Scheme.{u}} (f : ∀ a, Y a ⟶ T)
    (hcompat : ∀ a ∈ S, ∀ b ∈ S,
      pullback.fst (i a) (i b) ≫ f a = pullback.snd (i a) (i b) ≫ f b) :
    ∃ d : unionScheme i S ⟶ T,
      ∀ a (ha : a ∈ S), componentToUnion i S a ha ≫ d = f a := by
  classical
  revert hpartial hcompat
  induction S using Finset.induction_on with
  | empty =>
      intro hpartial hcompat
      refine ⟨(emptyUnionIsInitial i).to T, ?_⟩
      intro a ha
      exact (Finset.notMem_empty a ha).elim
  | @insert a S ha ih =>
      intro hpartial hcompat
      have hpartialS : ∀ U : Finset ι, U ⊆ S → ∀ b ∈ S, b ∉ U →
          IsReduced (pullback (unionMap i U) (i b)) := by
        intro U hU b hb hbU
        exact hpartial U (hU.trans (Finset.subset_insert a S)) b
          (Finset.mem_insert_of_mem hb) hbU
      obtain ⟨d, hd⟩ := ih hpartialS (fun b hb c hc =>
        hcompat b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
      let : IsReduced (pullback (unionMap i S) (i a)) :=
        hpartial S (Finset.subset_insert a S) a (Finset.mem_insert_self a S) ha
      let : ∀ b : {b : ι // b ∈ S}, IsReduced (pullback (i b.val) (i a)) := by
        intro b
        apply pair_reduced_of_singleton i a b.val
        apply hpartial {b.val}
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem b.property))
          a (Finset.mem_insert_self a S)
        intro hab
        apply ha
        rw [Finset.mem_singleton.mp hab]
        exact b.property
      have hover : pullback.fst (unionMap i S) (i a) ≫ d =
          pullback.snd (unionMap i S) (i a) ≫ f a := by
        apply partialOverlap_hom_ext i S a
        intro b hb
        simp only [pairToOverlap_fst_assoc, pairToOverlap_snd_assoc, hd b hb]
        exact hcompat b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a S)
      have hstep :
          pullback.fst (unionInclusion i (Finset.subset_insert a S))
            (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) ≫ d =
          pullback.snd (unionInclusion i (Finset.subset_insert a S))
            (componentToUnion i (insert a S) a (Finset.mem_insert_self a S)) ≫ f a := by
        simpa only [insertOverlapToAmbient_fst_assoc, insertOverlapToAmbient_snd_assoc] using
          congrArg (fun q : pullback (unionMap i S) (i a) ⟶ T =>
            insertOverlapToAmbient i S a ≫ q) hover
      obtain ⟨d', hleft, hright⟩ := ReducedClosedUnion.exists_desc
        (unionInclusion i (Finset.subset_insert a S))
        (componentToUnion i (insert a S) a (Finset.mem_insert_self a S))
        (insert_ranges_cover i S a) d (f a) hstep
      refine ⟨d', ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hright
      · calc
          componentToUnion i (insert a S) b _ ≫ d' =
              componentToUnion i S b hb ≫ d := by
            simpa only [← Category.assoc, componentToUnion_naturality] using
              congrArg (fun q : unionScheme i S ⟶ T =>
                componentToUnion i S b hb ≫ q) hleft
          _ = f b := hd b hb

variable (S : Finset ι)
  (hpartial : ∀ U : Finset ι, U ⊆ S → ∀ a ∈ S, a ∉ U →
    IsReduced (pullback (unionMap i U) (i a)))
  {T : Scheme.{u}} (f : ∀ a, Y a ⟶ T)
  (hcompat : ∀ a ∈ S, ∀ b ∈ S,
    pullback.fst (i a) (i b) ≫ f a = pullback.snd (i a) (i b) ≫ f b)

/-- Descent on the actual ideal-defined finite union. -/
def unionDesc : unionScheme i S ⟶ T := (exists_union_desc i S hpartial f hcompat).choose

omit [DecidableEq ι] in
@[reassoc (attr := simp)]
lemma componentToUnion_unionDesc (a : ι) (ha : a ∈ S) :
    componentToUnion i S a ha ≫ unionDesc i S hpartial f hcompat = f a :=
  (exists_union_desc i S hpartial f hcompat).choose_spec a ha

omit [DecidableEq ι] in
lemma unionDesc_unique (d : unionScheme i S ⟶ T)
    (hd : ∀ a (ha : a ∈ S), componentToUnion i S a ha ≫ d = f a) :
    d = unionDesc i S hpartial f hcompat := by
  apply union_hom_ext i S
  intro a ha
  simpa using hd a ha

omit [DecidableEq ι] in
@[reassoc]
lemma unionDesc_base {B : Scheme.{u}} (t : T ⟶ B) (s : X ⟶ B)
    (hf : ∀ a ∈ S, f a ≫ t = i a ≫ s) :
    unionDesc i S hpartial f hcompat ≫ t = unionMap i S ≫ s := by
  apply union_hom_ext i S
  intro a ha
  simpa using hf a ha

variable [IsReduced X]
  (hcover : (⋃ a : {a : ι // a ∈ S}, Set.range (i a.val)) = Set.univ)

/-- Descent to the original reduced ambient scheme, preserving original maps. -/
def desc : X ⟶ T :=
  (fullUnionIso i S hcover).inv ≫ unionDesc i S hpartial f hcompat

omit [DecidableEq ι] in
@[reassoc (attr := simp)]
lemma unionMap_desc :
    unionMap i S ≫ desc i S hpartial f hcompat hcover = unionDesc i S hpartial f hcompat := by
  change (fullUnionIso i S hcover).hom ≫ (fullUnionIso i S hcover).inv ≫ _ = _
  simp

omit [DecidableEq ι] in
@[reassoc (attr := simp)]
lemma inclusion_desc (a : ι) (ha : a ∈ S) :
    i a ≫ desc i S hpartial f hcompat hcover = f a := by
  rw [← componentToUnion_triangle i S a ha, Category.assoc, unionMap_desc,
    componentToUnion_unionDesc]

omit [DecidableEq ι] in
lemma desc_unique (d : X ⟶ T) (hd : ∀ a ∈ S, i a ≫ d = f a) :
    d = desc i S hpartial f hcompat hcover := by
  apply hom_ext i S hcover
  intro a ha
  exact (hd a ha).trans (inclusion_desc i S hpartial f hcompat hcover a ha).symm

omit [DecidableEq ι] in
/-- Exact arbitrary-base triangle, derived by the proved finite joint uniqueness. -/
@[reassoc]
lemma desc_base {B : Scheme.{u}} (t : T ⟶ B) (s : X ⟶ B)
    (hf : ∀ a ∈ S, f a ≫ t = i a ≫ s) :
    desc i S hpartial f hcompat hcover ≫ t = s := by
  apply hom_ext i S hcover
  intro a ha
  rw [← Category.assoc, inclusion_desc i S hpartial f hcompat hcover a ha]
  exact hf a ha

include hpartial hcompat hcover in
omit [DecidableEq ι] in
theorem exists_desc : ∃ d : X ⟶ T, ∀ a ∈ S, i a ≫ d = f a :=
  ⟨desc i S hpartial f hcompat hcover, inclusion_desc i S hpartial f hcompat hcover⟩

end AlgebraicGeometry.Scheme.FiniteClosedCover

end -- original EOF scope

end


section

/-!
Both partial-overlap reducedness obligations and both full-pullback
omit [DecidableEq ι] in
compatibilities remain actual inputs. No polygon/recognition theorem is assumed.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteClosedCover.Isomorphism
open AlgebraicGeometry.Scheme.FiniteClosedCover

variable {ι : Type v} [DecidableEq ι]
  {X Z : Scheme.{u}} [IsReduced X] [IsReduced Z]
  {Y W : ι → Scheme.{u}}
  (i : ∀ a, Y a ⟶ X) (j : ∀ a, W a ⟶ Z)
  [∀ a, IsClosedImmersion (i a)] [∀ a, IsClosedImmersion (j a)]
  [∀ a, IsReduced (Y a)]
  (e : ∀ a, Y a ≅ W a) (S : Finset ι)
  (hpartialX : ∀ U : Finset ι, U ⊆ S → ∀ a ∈ S, a ∉ U →
    IsReduced (pullback (unionMap i U) (i a)))
  (hpartialZ : ∀ U : Finset ι, U ⊆ S → ∀ a ∈ S, a ∉ U →
    IsReduced (pullback (unionMap j U) (j a)))
  (hforward : ∀ a ∈ S, ∀ b ∈ S,
    pullback.fst (i a) (i b) ≫ (e a).hom ≫ j a =
      pullback.snd (i a) (i b) ≫ (e b).hom ≫ j b)
  (hbackward : ∀ a ∈ S, ∀ b ∈ S,
    pullback.fst (j a) (j b) ≫ (e a).inv ≫ i a =
      pullback.snd (j a) (j b) ≫ (e b).inv ≫ i b)
  (hcoverX : (⋃ a : {a : ι // a ∈ S}, Set.range (i a.val)) = Set.univ)
  (hcoverZ : (⋃ a : {a : ι // a ∈ S}, Set.range (j a.val)) = Set.univ)

include e in
omit [DecidableEq ι] in
/-- Target component reducedness is derived from the supplied actual isomorphism. -/
lemma targetComponent_reduced (a : ι) : IsReduced (W a) :=
  isReduced_of_isOpenImmersion (e a).inv

/-- Forward descent along the actual source closed cover. -/
def forward : X ⟶ Z :=
  desc i S hpartialX (fun a => (e a).hom ≫ j a) hforward hcoverX

/-- Reverse descent keeps its own partial-overlap and full-pullback hypotheses. -/
def backward : Z ⟶ X := by
  let : ∀ a, IsReduced (W a) := targetComponent_reduced e
  exact desc j S hpartialZ (fun a => (e a).inv ≫ i a) hbackward hcoverZ

omit [IsReduced Z]
    [∀ a, IsClosedImmersion (j a)] in
omit [DecidableEq ι] in
@[reassoc] lemma inclusion_forward
    [IsReduced Z]
    [∀ a, IsClosedImmersion (j a)]
    (a : ι) (ha : a ∈ S) :
    i a ≫ forward i j e S hpartialX hforward hcoverX = (e a).hom ≫ j a :=
  inclusion_desc i S hpartialX (fun a => (e a).hom ≫ j a) hforward hcoverX a ha

omit [IsReduced X]
    [∀ a, IsClosedImmersion (i a)] in
omit [DecidableEq ι] in
@[reassoc] lemma inclusion_backward
    [IsReduced X]
    [∀ a, IsClosedImmersion (i a)]
    (a : ι) (ha : a ∈ S) :
    j a ≫ backward i j e S hpartialZ hbackward hcoverZ = (e a).inv ≫ i a := by
  let : ∀ a, IsReduced (W a) := targetComponent_reduced e
  exact inclusion_desc j S hpartialZ (fun a => (e a).inv ≫ i a) hbackward hcoverZ a ha

omit [DecidableEq ι] in
/-- The forward/reverse composites are identities on the same actual cover. -/
lemma forward_backward :
    forward i j e S hpartialX hforward hcoverX ≫
      backward i j e S hpartialZ hbackward hcoverZ = 𝟙 X := by
  apply FiniteClosedCover.hom_ext i S hcoverX
  intro a ha
  rw [← Category.assoc, inclusion_forward i j e S hpartialX hforward hcoverX a ha,
    Category.assoc, inclusion_backward i j e S hpartialZ hbackward hcoverZ a ha]
  simp

omit [DecidableEq ι] in
lemma backward_forward :
    backward i j e S hpartialZ hbackward hcoverZ ≫
      forward i j e S hpartialX hforward hcoverX = 𝟙 Z := by
  let : ∀ a, IsReduced (W a) := targetComponent_reduced e
  apply FiniteClosedCover.hom_ext j S hcoverZ
  intro a ha
  rw [← Category.assoc, inclusion_backward i j e S hpartialZ hbackward hcoverZ a ha,
    Category.assoc, inclusion_forward i j e S hpartialX hforward hcoverX a ha]
  simp

/-- Genuine ambient scheme isomorphism, obtained from the two actual descents. -/
def schemeIso : X ≅ Z where
  hom := forward i j e S hpartialX hforward hcoverX
  inv := backward i j e S hpartialZ hbackward hcoverZ
  hom_inv_id := forward_backward i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
  inv_hom_id := backward_forward i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ

omit [DecidableEq ι] in
@[reassoc] lemma schemeIso_hom_component (a : ι) (ha : a ∈ S) :
    i a ≫ (schemeIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ).hom =
      (e a).hom ≫ j a :=
  inclusion_forward i j e S hpartialX hforward hcoverX a ha

omit [DecidableEq ι] in
@[reassoc] lemma schemeIso_inv_component (a : ι) (ha : a ∈ S) :
    j a ≫ (schemeIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ).inv =
      (e a).inv ≫ i a :=
  inclusion_backward i j e S hpartialZ hbackward hcoverZ a ha

variable {B : Scheme.{u}} (sx : X ⟶ B) (tz : Z ⟶ B)
  (hbase : ∀ a ∈ S, (e a).hom ≫ j a ≫ tz = i a ≫ sx)

include hbase in
omit [IsReduced X]
    [IsReduced Z]
    [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsClosedImmersion (j a)]
    [∀ a, IsReduced (Y a)] in
omit [DecidableEq ι] in
/-- One component base triangle suffices; the reverse one is proved. -/
@[reassoc] lemma component_inverse_over
    [IsReduced X]
    [IsReduced Z]
    [∀ a, IsClosedImmersion (i a)]
    [∀ a, IsClosedImmersion (j a)]
    [∀ a, IsReduced (Y a)]
    (a : ι) (ha : a ∈ S) :
    (e a).inv ≫ i a ≫ sx = j a ≫ tz := by
  rw [← hbase a ha]
  simp

include hbase in
omit [IsReduced Z]
    [∀ a, IsClosedImmersion (j a)] in
omit [DecidableEq ι] in
@[reassoc] lemma forward_over
    [IsReduced Z]
    [∀ a, IsClosedImmersion (j a)]
    :
    forward i j e S hpartialX hforward hcoverX ≫ tz = sx := by
  apply desc_base i S hpartialX (fun a => (e a).hom ≫ j a) hforward hcoverX tz sx
  intro a ha
  simpa only [Category.assoc] using hbase a ha

include hbase in
omit [DecidableEq ι] in
@[reassoc] lemma backward_over :
    backward i j e S hpartialZ hbackward hcoverZ ≫ sx = tz := by
  let : ∀ a, IsReduced (W a) := targetComponent_reduced e
  apply desc_base j S hpartialZ (fun a => (e a).inv ≫ i a) hbackward hcoverZ sx tz
  intro a ha
  simpa only [Category.assoc] using component_inverse_over i j e S sx tz hbase a ha

/-- The actual Over-base isomorphism; no global recognition premise is used. -/
def overIso : Over.mk sx ≅ Over.mk tz := by
  let z : X ≅ Z := schemeIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
  exact Over.isoMk z (forward_over i j e S hpartialX hforward hcoverX sx tz hbase)

omit [DecidableEq ι] in
@[reassoc] lemma overIso_hom_component (a : ι) (ha : a ∈ S) :
    i a ≫ (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
      sx tz hbase).hom.left = (e a).hom ≫ j a :=
  inclusion_forward i j e S hpartialX hforward hcoverX a ha

omit [DecidableEq ι] in
@[reassoc] lemma overIso_inv_component (a : ι) (ha : a ∈ S) :
    j a ≫ (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
      sx tz hbase).inv.left = (e a).inv ≫ i a :=
  inclusion_backward i j e S hpartialZ hbackward hcoverZ a ha

omit [DecidableEq ι] in
@[reassoc] lemma overIso_hom_over :
    (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
      sx tz hbase).hom.left ≫ tz = sx :=
  (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
    sx tz hbase).hom.w

omit [DecidableEq ι] in
@[reassoc] lemma overIso_inv_over :
    (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
      sx tz hbase).inv.left ≫ sx = tz :=
  (overIso i j e S hpartialX hpartialZ hforward hbackward hcoverX hcoverZ
    sx tz hbase).inv.w

end AlgebraicGeometry.Scheme.FiniteClosedCover.Isomorphism
end -- noncomputable section

end
