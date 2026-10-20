/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Components
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.Transport

/-!
# Literal one-gon and two-gon residue fibres

Source: frozen R5 `LocalModels/Incidence/SpecialFiber.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- A literal geometric subcase: an actual isomorphism of the actual residue
pullback with the explicitly constructed proper one-gon. This is supplied data,
not a theorem classifying arbitrary special fibres. The isomorphism is of the
whole special fibre; an isomorphism only of its reduction does not suffice. -/
abbrev OneGonIso := Over.mk (structureMap π) ≅
  Over.mk (Scheme.PinchedLine.pinchedStructure (IsLocalRing.ResidueField R))

/-- The corresponding literal two-gon geometric subcase. -/
abbrev TwoGonIso := Over.mk (structureMap π) ≅
  Over.mk (Scheme.TwoGon.structureMap (IsLocalRing.ResidueField R))

/-- The projective-line normalization mapped to the actual one-gon residue fibre via `e`. -/
def oneGonNormalization (e : OneGonIso π) :
    Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) ⟶ (obj π) :=
  Scheme.PinchedLine.gluedNormalizationMap (IsLocalRing.ResidueField R) ≫ e.inv.left

/-- The transported one-gon normalization is finite. -/
instance oneGonNormalization_finite (e : OneGonIso π) :
    IsFinite (oneGonNormalization π e) := by
  unfold oneGonNormalization
  infer_instance

/-- The transported one-gon normalization is surjective. -/
instance oneGonNormalization_surjective (e : OneGonIso π) :
    Surjective (oneGonNormalization π e) := by
  unfold oneGonNormalization
  infer_instance

@[reassoc] theorem oneGonNormalization_over (e : OneGonIso π) :
    oneGonNormalization π e ≫ (structureMap π) =
      Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) := by
  rw [oneGonNormalization, Category.assoc]
  exact (congrArg (Scheme.PinchedLine.gluedNormalizationMap _ ≫ ·) (Over.w e.inv)).trans
    (Scheme.PinchedLine.gluedNormalizationMap_over _)

theorem oneGon_components_card (e : OneGonIso π) :
    Nat.card (irreducibleComponents (obj π)) = 1 := by
  exact (Nat.card_congr (componentsEquiv ((Over.forget _).mapIso e))).trans
    (Scheme.PinchedLine.pinchedGluing_components_card _)

theorem oneGon_node_fibre_card (e : OneGonIso π) :
    Nat.card {z // oneGonNormalization π e z =
      e.inv.left (Scheme.PinchedLine.gluedNodePoint (IsLocalRing.ResidueField R))} = 2 := by
  exact (Nat.card_congr (Scheme.fibreEquivOfTargetIso
    (Scheme.PinchedLine.gluedNormalizationMap (IsLocalRing.ResidueField R))
    ((Over.forget _).mapIso e) (Scheme.PinchedLine.gluedNodePoint (IsLocalRing.ResidueField
      R)))).trans
    (Scheme.PinchedLine.glued_normalization_fibre_card _)

theorem oneGon_specialFiber_reduced (e : OneGonIso π) : IsReduced (obj π) := by
  let : IsReduced (Over.mk (Scheme.PinchedLine.pinchedStructure (IsLocalRing.ResidueField
    R))).left := by
    change IsReduced (Scheme.PinchedLine.pinchedGluing (IsLocalRing.ResidueField R))
    infer_instance
  exact isReduced_of_isOpenImmersion e.hom.left

/-- The two branch points remain actual points of the normal projective line. -/
theorem oneGon_node_fibre (e : OneGonIso π)
    (z : Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R)) :
    oneGonNormalization π e z =
      e.inv.left (Scheme.PinchedLine.gluedNodePoint (IsLocalRing.ResidueField R)) ↔
      z = Scheme.PinchedLine.gluedBranchPoint (IsLocalRing.ResidueField R) 0 ∨
      z = Scheme.PinchedLine.gluedBranchPoint (IsLocalRing.ResidueField R) 1 := by
  change e.inv.left (Scheme.PinchedLine.gluedNormalizationMap _ z) = e.inv.left _ ↔ _
  exact e.inv.left.homeomorph.injective.eq_iff.trans
    (Scheme.PinchedLine.glued_normalization_fibre _ z)

open Scheme.TwoGon

/-- The two-component normalization mapped to the actual two-gon residue fibre via `e`. -/
def twoGonNormalization (e : TwoGonIso π) :
    normalized (IsLocalRing.ResidueField R) ⟶ (obj π) :=
  normalization (IsLocalRing.ResidueField R) ≫ e.inv.left

/-- The transported two-gon normalization is finite. -/
instance twoGonNormalization_finite (e : TwoGonIso π) :
    IsFinite (twoGonNormalization π e) := by
  unfold twoGonNormalization
  infer_instance

/-- The transported two-gon normalization is surjective. -/
instance twoGonNormalization_surjective (e : TwoGonIso π) :
    Surjective (twoGonNormalization π e) := by
  unfold twoGonNormalization
  infer_instance

@[reassoc] theorem twoGonNormalization_over (e : TwoGonIso π) :
    twoGonNormalization π e ≫ (structureMap π) =
      normalizedStructure (IsLocalRing.ResidueField R) := by
  rw [twoGonNormalization, Category.assoc]
  exact (congrArg (normalization _ ≫ ·) (Over.w e.inv)).trans (normalization_over _)

theorem twoGon_components_card (e : TwoGonIso π) :
    Nat.card (irreducibleComponents (obj π)) = 2 :=
  (Nat.card_congr (componentsEquiv ((Over.forget _).mapIso e))).trans
    (target_components_card _)

theorem twoGon_specialFiber_reduced (e : TwoGonIso π) : IsReduced (obj π) := by
  let : IsReduced (Over.mk (Scheme.TwoGon.structureMap (IsLocalRing.ResidueField R))).left := by
    change IsReduced (twoGon (IsLocalRing.ResidueField R))
    infer_instance
  exact isReduced_of_isOpenImmersion e.hom.left

/-- The point obtained by transporting the two-gon intersection point with parameter `a`. -/
def twoGonNode (e : TwoGonIso π) (a : IsLocalRing.ResidueField R) : (obj π) :=
  e.inv.left (intersectionPoint (IsLocalRing.ResidueField R) a)

theorem twoGon_nodes_distinct (e : TwoGonIso π) : twoGonNode π e 0 ≠ twoGonNode π e 1 :=
  fun h => intersectionPoints_distinct _ (e.inv.left.homeomorph.injective h)

theorem twoGon_node_fibre (e : TwoGonIso π) (a : IsLocalRing.ResidueField R)
    (ha : a = 0 ∨ a = 1) (z : normalized (IsLocalRing.ResidueField R)) :
    twoGonNormalization π e z = twoGonNode π e a ↔
      z = leftPoint (IsLocalRing.ResidueField R) a ∨
      z = rightPoint (IsLocalRing.ResidueField R) a := by
  change e.inv.left (normalization _ z) = e.inv.left _ ↔ _
  exact e.inv.left.homeomorph.injective.eq_iff.trans (normalization_fibre _ a ha z)

theorem twoGon_node_fibre_card (e : TwoGonIso π) (a : IsLocalRing.ResidueField R)
    (ha : a = 0 ∨ a = 1) :
    Nat.card {z // twoGonNormalization π e z = twoGonNode π e a} = 2 :=
  (Nat.card_congr (Scheme.fibreEquivOfTargetIso
    (normalization (IsLocalRing.ResidueField R)) ((Over.forget _).mapIso e)
    (intersectionPoint (IsLocalRing.ResidueField R) a))).trans (normalization_fibre_card _ a ha)

/-- The component sets are transported along the literal special-fibre isomorphism. -/
def twoGonLeftComponent (e : TwoGonIso π) : Set (obj π) :=
  e.hom.left ⁻¹' targetLeftComponent (IsLocalRing.ResidueField R)
/-- The right two-gon component as a subset of the actual residue fibre. -/
def twoGonRightComponent (e : TwoGonIso π) : Set (obj π) :=
  e.hom.left ⁻¹' targetRightComponent (IsLocalRing.ResidueField R)

private theorem twoGon_hom_inv (e : TwoGonIso π) (y : twoGon (IsLocalRing.ResidueField R)) :
    e.hom.left (e.inv.left y) = y := by
  exact congrArg (fun f : twoGon (IsLocalRing.ResidueField R) ⟶ _ => f y)
    (congrArg Over.Hom.left e.inv_hom_id)

private theorem twoGon_inv_hom (e : TwoGonIso π) (y : (obj π)) :
    e.inv.left (e.hom.left y) = y := by
  exact congrArg (fun f : (obj π) ⟶ _ => f y)
    (congrArg Over.Hom.left e.hom_inv_id)

theorem twoGon_components_cover (e : TwoGonIso π) :
    twoGonLeftComponent π e ∪ twoGonRightComponent π e = Set.univ := by
  change e.hom.left ⁻¹' targetLeftComponent _ ∪ e.hom.left ⁻¹' targetRightComponent _ = _
  rw [← Set.preimage_union, target_components_cover, Set.preimage_univ]

/-- These two transported sets are exactly the irreducible components of the
actual special fibre, not merely a pair of covering subsets. -/
theorem twoGon_components_eq (e : TwoGonIso π) :
    irreducibleComponents (obj π) =
      {twoGonLeftComponent π e, twoGonRightComponent π e} := by
  apply _root_.irreducibleComponents_eq_pair
  · exact (targetLeft_isClosed _).preimage e.hom.left.continuous
  · exact (targetRight_isClosed _).preimage e.hom.left.continuous
  · apply (targetLeft_irreducible _).preimage e.hom.left.isOpenEmbedding
    obtain ⟨y, hy⟩ := (targetLeft_irreducible (IsLocalRing.ResidueField R)).nonempty
    exact ⟨y, hy, e.inv.left y, twoGon_hom_inv π e y⟩
  · apply (targetRight_irreducible _).preimage e.hom.left.isOpenEmbedding
    obtain ⟨y, hy⟩ := (targetRight_irreducible (IsLocalRing.ResidueField R)).nonempty
    exact ⟨y, hy, e.inv.left y, twoGon_hom_inv π e y⟩
  · exact twoGon_components_cover π e
  · intro h
    apply target_left_not_subset_right (IsLocalRing.ResidueField R)
    intro y hy
    have : e.inv.left y ∈ twoGonLeftComponent π e := by
      simpa only [twoGonLeftComponent, Set.mem_preimage, twoGon_hom_inv] using hy
    have h' := h this
    simpa only [twoGonRightComponent, Set.mem_preimage, twoGon_hom_inv] using h'
  · intro h
    apply target_right_not_subset_left (IsLocalRing.ResidueField R)
    intro y hy
    have : e.inv.left y ∈ twoGonRightComponent π e := by
      simpa only [twoGonRightComponent, Set.mem_preimage, twoGon_hom_inv] using hy
    have h' := h this
    simpa only [twoGonLeftComponent, Set.mem_preimage, twoGon_hom_inv] using h'

theorem twoGon_components_intersection (e : TwoGonIso π) :
    twoGonLeftComponent π e ∩ twoGonRightComponent π e =
      {twoGonNode π e 0, twoGonNode π e 1} := by
  change e.hom.left ⁻¹' targetLeftComponent _ ∩ e.hom.left ⁻¹' targetRightComponent _ = _
  rw [← Set.preimage_inter, target_components_intersection]
  ext z
  change (e.hom.left z = intersectionPoint _ 0 ∨ e.hom.left z = intersectionPoint _ 1) ↔ _
  constructor
  · rintro (h | h)
    · left; exact (twoGon_inv_hom π e z).symm.trans (congrArg e.inv.left h)
    · right; exact (twoGon_inv_hom π e z).symm.trans (congrArg e.inv.left h)
  · rintro (rfl | rfl)
    · exact Or.inl (twoGon_hom_inv π e _)
    · exact Or.inr (twoGon_hom_inv π e _)

theorem twoGon_components_intersection_card (e : TwoGonIso π) :
    (twoGonLeftComponent π e ∩ twoGonRightComponent π e).ncard = 2 := by
  rw [twoGon_components_intersection, Set.ncard_pair (twoGon_nodes_distinct π e)]

/-- The left component has precisely the two constructed normalized branches. -/
theorem twoGon_left_branchSet (e : TwoGonIso π) :
    {z : normalized (IsLocalRing.ResidueField R) |
      z ∈ Set.range (leftComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e} =
      {leftPoint (IsLocalRing.ResidueField R) 0, leftPoint (IsLocalRing.ResidueField R) 1} := by
  have h : ∀ z, e.hom.left (twoGonNormalization π e z) = normalization _ z :=
    fun z => twoGon_hom_inv π e _
  simp only [twoGonLeftComponent, twoGonRightComponent, Set.mem_inter_iff, Set.mem_preimage, h]
  exact left_branchSet _

/-- The right component has precisely the two constructed normalized branches. -/
theorem twoGon_right_branchSet (e : TwoGonIso π) :
    {z : normalized (IsLocalRing.ResidueField R) |
      z ∈ Set.range (rightComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e} =
      {rightPoint (IsLocalRing.ResidueField R) 0, rightPoint (IsLocalRing.ResidueField R) 1} := by
  have h : ∀ z, e.hom.left (twoGonNormalization π e z) = normalization _ z :=
    fun z => twoGon_hom_inv π e _
  simp only [twoGonLeftComponent, twoGonRightComponent, Set.mem_inter_iff, Set.mem_preimage, h]
  exact right_branchSet _

theorem twoGon_left_branchSet_card (e : TwoGonIso π) :
    {z : normalized (IsLocalRing.ResidueField R) |
      z ∈ Set.range (leftComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e}.ncard = 2
        := by
  rw [twoGon_left_branchSet, Set.ncard_pair (leftEndpoints_distinct _)]

theorem twoGon_right_branchSet_card (e : TwoGonIso π) :
    {z : normalized (IsLocalRing.ResidueField R) |
      z ∈ Set.range (rightComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e}.ncard = 2
        := by
  rw [twoGon_right_branchSet, Set.ncard_pair (rightEndpoints_distinct _)]

/-- The transported left projective-line component is an actual closed immersion
into the same special fibre. -/
def twoGonLeftComponentMap (e : TwoGonIso π) :
    Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) ⟶ (obj π) :=
  leftTargetMap (IsLocalRing.ResidueField R) ≫ e.inv.left

/-- The right projective-line component mapped into the actual two-gon residue fibre. -/
def twoGonRightComponentMap (e : TwoGonIso π) :
    Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) ⟶ (obj π) :=
  rightTargetMap (IsLocalRing.ResidueField R) ≫ e.inv.left

/-- The left parametrized component is a closed subscheme of the actual two-gon fibre. -/
instance twoGonLeftComponentMap_closed (e : TwoGonIso π) :
    IsClosedImmersion (twoGonLeftComponentMap π e) := by
  unfold twoGonLeftComponentMap
  infer_instance

/-- The right parametrized component is a closed subscheme of the actual two-gon fibre. -/
instance twoGonRightComponentMap_closed (e : TwoGonIso π) :
    IsClosedImmersion (twoGonRightComponentMap π e) := by
  unfold twoGonRightComponentMap
  infer_instance

@[reassoc] theorem twoGonLeftComponentMap_over (e : TwoGonIso π) :
    twoGonLeftComponentMap π e ≫ (structureMap π) =
      Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) := by
  rw [twoGonLeftComponentMap, Category.assoc]
  exact (congrArg (leftTargetMap _ ≫ ·) (Over.w e.inv)).trans (leftTargetMap_over _)

@[reassoc] theorem twoGonRightComponentMap_over (e : TwoGonIso π) :
    twoGonRightComponentMap π e ≫ (structureMap π) =
      Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) := by
  rw [twoGonRightComponentMap, Category.assoc]
  exact (congrArg (rightTargetMap _ ≫ ·) (Over.w e.inv)).trans (rightTargetMap_over _)

/-- The closed image scheme of the left component in the actual two-gon fibre. -/
abbrev twoGonLeftComponentScheme (e : TwoGonIso π) : Scheme.{u} :=
  (twoGonLeftComponentMap π e).image
/-- The closed image scheme of the right component in the actual two-gon fibre. -/
abbrev twoGonRightComponentScheme (e : TwoGonIso π) : Scheme.{u} :=
  (twoGonRightComponentMap π e).image

/-- The left closed component image identified with the projective line over the residue field. -/
def twoGonLeftComponentSchemeIsoP1 (e : TwoGonIso π) :
    twoGonLeftComponentScheme π e ≅ Scheme.ProjectiveLine.projectiveP1
      (IsLocalRing.ResidueField R) :=
  (asIso (twoGonLeftComponentMap π e).toImage).symm ≪≫
    Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _

/-- The right closed component image identified with the projective line over the residue field. -/
def twoGonRightComponentSchemeIsoP1 (e : TwoGonIso π) :
    twoGonRightComponentScheme π e ≅ Scheme.ProjectiveLine.projectiveP1
      (IsLocalRing.ResidueField R) :=
  (asIso (twoGonRightComponentMap π e).toImage).symm ≪≫
    Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _

/-- The left closed component image of the actual two-gon fibre is reduced. -/
instance twoGonLeftComponentScheme_reduced (e : TwoGonIso π) :
    IsReduced (twoGonLeftComponentScheme π e) :=
  isReduced_of_isOpenImmersion (asIso (twoGonLeftComponentMap π e).toImage).inv

/-- The right closed component image of the actual two-gon fibre is reduced. -/
instance twoGonRightComponentScheme_reduced (e : TwoGonIso π) :
    IsReduced (twoGonRightComponentScheme π e) :=
  isReduced_of_isOpenImmersion (asIso (twoGonRightComponentMap π e).toImage).inv

theorem twoGonLeftComponentMap_range (e : TwoGonIso π) :
    Set.range (twoGonLeftComponentMap π e) = twoGonLeftComponent π e := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change e.hom.left (e.inv.left (leftTargetMap _ x)) ∈ targetLeftComponent _
    rw [twoGon_hom_inv, ← leftTargetMap_range]
    exact ⟨x, rfl⟩
  · intro hz
    change e.hom.left z ∈ targetLeftComponent (IsLocalRing.ResidueField R) at hz
    rw [← leftTargetMap_range] at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, (congrArg e.inv.left hx).trans (twoGon_inv_hom π e z)⟩

theorem twoGonRightComponentMap_range (e : TwoGonIso π) :
    Set.range (twoGonRightComponentMap π e) = twoGonRightComponent π e := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change e.hom.left (e.inv.left (rightTargetMap _ x)) ∈ targetRightComponent _
    rw [twoGon_hom_inv, ← rightTargetMap_range]
    exact ⟨x, rfl⟩
  · intro hz
    change e.hom.left z ∈ targetRightComponent (IsLocalRing.ResidueField R) at hz
    rw [← rightTargetMap_range] at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, (congrArg e.inv.left hx).trans (twoGon_inv_hom π e z)⟩

theorem twoGonLeftComponentScheme_range (e : TwoGonIso π) :
    Set.range (twoGonLeftComponentMap π e).imageι = twoGonLeftComponent π e := by
  change Set.range (twoGonLeftComponentMap π e).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    (twoGonLeftComponentMap π e).isClosedEmbedding.isClosed_range.closure_eq,
    twoGonLeftComponentMap_range]

theorem twoGonRightComponentScheme_range (e : TwoGonIso π) :
    Set.range (twoGonRightComponentMap π e).imageι = twoGonRightComponent π e := by
  change Set.range (twoGonRightComponentMap π e).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    (twoGonRightComponentMap π e).isClosedEmbedding.isClosed_range.closure_eq,
    twoGonRightComponentMap_range]

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
end
