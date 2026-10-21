/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.Complement
public import Aglib.AlgebraicGeometry.Gluing.FiniteClosedCover
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.TwoPointSubscheme
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.IntersectionComparison

/-!
# Finite subsets of the actual component family

Finite subsets use the canonical native unionIdeal, unionScheme and unionMap, with exactly the
original component kernels. A supplied actual complement/two-point isomorphism proves reducedness
of each required partial overlap. Reindexing uses precisely Finset.map e.toEmbedding and the
resulting native finite closed descent.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/Incidence/FiniteClosedCover.lean`: source ranges [[47, 242], [275, 372]];
SHA-256 `e8b461f107b1c6de51707df54615d8bbdf439d26277385d9f8e9312155c1d84c`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open Scheme.IdealSheafData Scheme.FiniteClosedCover
universe u v
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
  {C : irreducibleComponents (obj π) → Scheme.{u}}
  (i : ∀ v, C v ⟶ obj π)
  [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))]
  (hrange : ∀ v, Set.range (i v) = v.val)

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
lemma otherIdeal_le_subsetIdeal (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    otherIdeal π i v ≤ FiniteClosedCover.unionIdeal i S := by
  apply le_iInf
  intro w
  exact iInf_le_of_le ⟨w.val, fun h => hv (h ▸ w.property)⟩ le_rfl

/-- Literal ideal-induced inclusion into the native complementary union. -/
def subsetToOther (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    FiniteClosedCover.unionScheme i S ⟶ otherScheme π i v :=
  Scheme.IdealSheafData.inclusion (otherIdeal_le_subsetIdeal π i S v hv)

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
@[reassoc (attr := simp)] lemma subsetToOther_triangle
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    subsetToOther π i S v hv ≫ otherMap π i v = FiniteClosedCover.unionMap i S :=
  inclusion_subschemeι _

/-- A finite subset union excluding v is closed in the complementary union. -/
instance subsetToOther_closed (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    IsClosedImmersion (subsetToOther π i S v hv) := by
  have : IsClosedImmersion (subsetToOther π i S v hv ≫ otherMap π i v) := by
    rw [subsetToOther_triangle]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (otherMap π i v)

/-- The actual intersection of a finite kernel union with one selected component. -/
abbrev subsetIntersection (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) : Scheme.{u} :=
  pullback (FiniteClosedCover.unionMap i S) (i v)

/-- The induced map of actual pullbacks; no distribution of pullback over infima. -/
def subsetIntersectionToOther (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    subsetIntersection π i S v ⟶ componentOtherIntersection π i v :=
  pullback.lift
    (pullback.fst _ _ ≫ subsetToOther π i S v hv)
    (pullback.snd _ _) (by
      simp only [Category.assoc, subsetToOther_triangle]
      exact pullback.condition)

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
@[reassoc (attr := simp)] lemma subsetIntersectionToOther_snd
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    subsetIntersectionToOther π i S v hv ≫ pullback.snd _ _ =
      pullback.snd (FiniteClosedCover.unionMap i S) (i v) := pullback.lift_snd ..

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
@[reassoc (attr := simp)] lemma subsetIntersectionToOther_fst
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    subsetIntersectionToOther π i S v hv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ subsetToOther π i S v hv := pullback.lift_fst ..

/-- The induced actual overlap map is a closed immersion. -/
instance subsetIntersectionToOther_closed
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S) :
    IsClosedImmersion (subsetIntersectionToOther π i S v hv) := by
  have : IsClosedImmersion (subsetIntersectionToOther π i S v hv ≫
      pullback.snd (otherMap π i v) (i v)) := by
    rw [subsetIntersectionToOther_snd]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.snd (otherMap π i v) (i v))

/-- The actual partial overlap maps into the supplied structural two-point intersection. -/
def subsetIntersectionToTwoPoints
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S)
    (e : componentOtherTwoPointIso π i v) :
    subsetIntersection π i S v ⟶
      Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  subsetIntersectionToOther π i S v hv ≫ e.hom.left

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
@[reassoc] lemma subsetIntersectionToTwoPoints_over
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S)
    (e : componentOtherTwoPointIso π i v) :
    subsetIntersectionToTwoPoints π i S v hv e ≫
      Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      pullback.snd (FiniteClosedCover.unionMap i S) (i v) ≫ structureMap π i v := by
  have he : e.hom.left ≫ Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      componentOtherIntersectionStructure π i v := Over.w e.hom
  simp only [subsetIntersectionToTwoPoints, Category.assoc, he,
    componentOtherIntersectionStructure, subsetIntersectionToOther_snd_assoc]

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
/-- Every actual partial overlap is reduced under its actual complement two-point iso. -/
theorem subsetIntersection_reduced
    (S : Finset (irreducibleComponents (obj π)))
    (v : irreducibleComponents (obj π)) (hv : v ∉ S)
    (e : componentOtherTwoPointIso π i v) : IsReduced (subsetIntersection π i S v) := by
  let j := subsetIntersectionToTwoPoints π i S v hv e
  have : IsClosedImmersion j := by
    let e' := (Over.forget _).mapIso e
    change IsClosedImmersion (subsetIntersectionToOther π i S v hv ≫ e'.hom)
    infer_instance
  exact Scheme.TwoPoint.reduced_of_closed_into_twoPoints _ j

variable {ι : Type v} (e : ι ≃ irreducibleComponents (obj π))

omit [Finite (irreducibleComponents (obj π))] in
/-- The precise finite kernel-inf reindexing, not a support-only equality. -/
lemma reindexedUnionIdeal_eq_native (S : Finset ι) :
    unionIdeal (fun a => i (e a)) S =
      FiniteClosedCover.unionIdeal i (S.map e.toEmbedding) := by
  apply le_antisymm
  · apply le_iInf
    intro w
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp w.property
    change unionIdeal (fun a => i (e a)) S ≤ (i w.val).ker
    rw [← he]
    exact unionIdeal_le_component (fun a => i (e a)) S a ha
  · apply le_iInf
    intro a
    exact iInf_le (fun w : {w : irreducibleComponents (obj π) //
        w ∈ S.map e.toEmbedding} => (i w.val).ker)
      ⟨e a.val, Finset.mem_map.mpr ⟨a.val, a.property, rfl⟩⟩

/-- The actual closed union comparison induced by the exact finite kernel reindexing. -/
def reindexedUnionIso (S : Finset ι) :
    unionScheme (fun a => i (e a)) S ≅
      FiniteClosedCover.unionScheme i (S.map e.toEmbedding) :=
  Scheme.IdealSheafData.subschemeIsoOfEq (reindexedUnionIdeal_eq_native π i e S)

omit [Finite (irreducibleComponents (obj π))] in
@[reassoc (attr := simp)] lemma reindexedUnionIso_triangle (S : Finset ι) :
    (reindexedUnionIso π i e S).hom ≫ FiniteClosedCover.unionMap i (S.map e.toEmbedding) =
      unionMap (fun a => i (e a)) S :=
  Scheme.IdealSheafData.subschemeIsoOfEq_hom_subschemeι _

omit [Finite (irreducibleComponents (obj π))] in
/-- Actual component pullback reducedness survives the exact ideal reindexing. -/
lemma reindexedPartialOverlap_reduced (S : Finset ι) (a : ι) (ha : a ∉ S)
    (native : componentOtherTwoPointIso π i (e a)) :
    IsReduced (pullback (unionMap (fun a => i (e a)) S) (i (e a))) := by
  have he : e a ∉ S.map e.toEmbedding := by
    intro h
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp h
    exact ha (e.injective hba ▸ hb)
  change IsReduced (pullback
    (unionIdeal (fun a => i (e a)) S).subschemeι (i (e a)))
  rw [reindexedUnionIdeal_eq_native π i e S]
  exact subsetIntersection_reduced π i (S.map e.toEmbedding) (e a) he native

omit [Finite (irreducibleComponents (obj π))] in
/-- Exact hpartial telescope of finite descent, discharged from native geometry.
The U⊆S and a∈S binders scope the consumer; reducedness holds whenever a∉U. -/
lemma reindexedPartialOverlap_family (S : Finset ι)
    (native : ∀ w, componentOtherTwoPointIso π i w) :
    ∀ U : Finset ι, U ⊆ S → ∀ a ∈ S, a ∉ U →
      IsReduced (pullback (unionMap (fun a => i (e a)) U) (i (e a))) := by
  intro U _ a _ ha
  exact reindexedPartialOverlap_reduced π i e U a ha (native (e a))

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
include hrange in
/-- A complete relabelling covers the same actual fibre. -/
lemma reindexed_components_cover [Fintype ι] :
    (⋃ a : {a : ι // a ∈ (Finset.univ : Finset ι)}, Set.range (i (e a.val))) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨w, hw⟩ := exhaustive π i hrange x
  refine Set.mem_iUnion.mpr ⟨⟨e.symm w, Finset.mem_univ _⟩, ?_⟩
  change x ∈ Set.range (i (e (e.symm w)))
  rw [e.apply_symm_apply]
  exact hw

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
/-- Exact original residue-field triangle for each reindexed component. -/
@[reassoc] lemma reindexed_component_structure (a : ι) :
    i (e a) ≫ (ResidueFiber.structureMap π) = structureMap π i (e a) := rfl

/-- Native finite descent is an application of the generic theorem, with its
actual partial-overlap hypothesis discharged rather than retained. -/
def nativeReindexedDesc [Fintype ι] [IsReduced (obj π)]
    (native : ∀ w, componentOtherTwoPointIso π i w)
    {T : Scheme.{u}} (f : ∀ a, C (e a) ⟶ T)
    (hcompat : ∀ a b, pullback.fst (i (e a)) (i (e b)) ≫ f a =
      pullback.snd (i (e a)) (i (e b)) ≫ f b) : (obj π) ⟶ T := by
  classical
  exact FiniteClosedCover.desc (fun a => i (e a)) Finset.univ
    (reindexedPartialOverlap_family π i e Finset.univ native) f
    (fun a _ b _ => hcompat a b) (reindexed_components_cover π i hrange e)

omit [Finite (irreducibleComponents (obj π))] in
@[reassoc (attr := simp)] lemma nativeReindexedDesc_component
    [Fintype ι] [IsReduced (obj π)]
    (native : ∀ w, componentOtherTwoPointIso π i w)
    {T : Scheme.{u}} (f : ∀ a, C (e a) ⟶ T)
    (hcompat : ∀ a b, pullback.fst (i (e a)) (i (e b)) ≫ f a =
      pullback.snd (i (e a)) (i (e b)) ≫ f b) (a : ι) :
    i (e a) ≫ nativeReindexedDesc π i hrange e native f hcompat = f a := by
  classical
  exact FiniteClosedCover.inclusion_desc _ _ _ _ _ _ a (Finset.mem_univ a)

omit [Finite (irreducibleComponents (obj π))] in
/-- Finite descent keeps the original residue field and the supplied target map. -/
@[reassoc] lemma nativeReindexedDesc_over
    [Fintype ι] [IsReduced (obj π)]
    (native : ∀ w, componentOtherTwoPointIso π i w)
    {T : Scheme.{u}} (f : ∀ a, C (e a) ⟶ T)
    (hcompat : ∀ a b, pullback.fst (i (e a)) (i (e b)) ≫ f a =
      pullback.snd (i (e a)) (i (e b)) ≫ f b)
    (t : T ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (hf : ∀ a, f a ≫ t = structureMap π i (e a)) :
    nativeReindexedDesc π i hrange e native f hcompat ≫ t = (ResidueFiber.structureMap π) := by
  classical
  apply FiniteClosedCover.desc_base
  intro a _
  exact hf a


end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
