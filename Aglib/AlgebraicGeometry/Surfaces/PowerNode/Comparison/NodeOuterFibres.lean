/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Limits.FiberChart
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.NodeSpecialFibres

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.NodeOuterFibres`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`ed68003b072eea058ef542158bdec13ca70718f5fce02647f7fa8ecef5b73c19`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode

/-!
# Base, end, and outer node fibres and explicit transitions

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section NodeResolutionBaseFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre Topology
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Pullback.Fibre
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)

/-- Identifies the exponent-zero special fibre with the spectrum of the Laurent polynomial ring
over the residue field. -/
def zeroSpecialFibreGmIso : sourceSpecialFibre (zero π) ≅
    Spec (.of (Localization.Away (Polynomial.X : (IsLocalRing.ResidueField R)[X]))) :=
  zeroSpecialFibreIso π ≪≫
    Scheme.Spec.mapIso (unitNodeLaurentEquiv (IsLocalRing.ResidueField
      R)).symm.toRingEquiv.toCommRingCatIso.op

lemma oneSpecialFibre_reduced : AlgebraicGeometry.IsReduced (sourceSpecialFibre (one π hπ)) :=
  isReduced_of_isOpenImmersion (oneSpecialFibreIso π hπ).hom

lemma one_components_cover (z : sourceSpecialFibre (one π hπ)) :
    z ∈ Set.range (oneLeftComponent π hπ) ∨ z ∈ Set.range (oneRightComponent π hπ) := by
  obtain ⟨x, rfl⟩ := (oneSpecialFibreIso π hπ).inv.surjective z
  rcases Cross.components_cover (IsLocalRing.ResidueField R) x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨p, rfl⟩
  · exact Or.inr ⟨p, rfl⟩

lemma oneLeft_range_irreducible : IsIrreducible (Set.range (oneLeftComponent π hπ)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Cross.line (IsLocalRing.ResidueField R))).image
      (oneLeftComponent π hπ) (oneLeftComponent π hπ).continuous.continuousOn
lemma oneRight_range_irreducible : IsIrreducible (Set.range (oneRightComponent π hπ)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Cross.line (IsLocalRing.ResidueField R))).image
      (oneRightComponent π hπ) (oneRightComponent π hπ).continuous.continuousOn

lemma oneLeft_not_subset_right :
    ¬Set.range (oneLeftComponent π hπ) ⊆ Set.range (oneRightComponent π hπ) := by
  intro h
  apply Cross.left_not_subset_right (IsLocalRing.ResidueField R)
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := h (show oneLeftComponent π hπ p ∈ Set.range (oneLeftComponent π hπ) from ⟨p,
    rfl⟩)
  exact ⟨q, (oneSpecialFibreIso π hπ).inv.isOpenEmbedding.injective hq⟩
lemma oneRight_not_subset_left :
    ¬Set.range (oneRightComponent π hπ) ⊆ Set.range (oneLeftComponent π hπ) := by
  intro h
  apply Cross.right_not_subset_left (IsLocalRing.ResidueField R)
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := h (show oneRightComponent π hπ p ∈ Set.range (oneRightComponent π hπ) from ⟨p,
    rfl⟩)
  exact ⟨q, (oneSpecialFibreIso π hπ).inv.isOpenEmbedding.injective hq⟩

lemma one_irreducible_subset_component {s : Set (sourceSpecialFibre (one π hπ))}
    (hs : IsIrreducible s) :
    s ⊆ Set.range (oneLeftComponent π hπ) ∨ s ⊆ Set.range (oneRightComponent π hπ) :=
  isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 _ _
    (oneLeftComponent π hπ).isClosedEmbedding.isClosed_range
    (oneRightComponent π hπ).isClosedEmbedding.isClosed_range
    (fun z _ => one_components_cover π hπ z)

lemma oneLeft_mem_irreducibleComponents :
    Set.range (oneLeftComponent π hπ) ∈ irreducibleComponents (sourceSpecialFibre (one π hπ)) := by
  refine ⟨oneLeft_range_irreducible π hπ, ?_⟩
  intro s hs hle
  rcases one_irreducible_subset_component π hπ hs with h | h
  · exact h
  · exact False.elim (oneLeft_not_subset_right π hπ (hle.trans h))
lemma oneRight_mem_irreducibleComponents :
    Set.range (oneRightComponent π hπ) ∈ irreducibleComponents (sourceSpecialFibre (one π hπ)) := by
  refine ⟨oneRight_range_irreducible π hπ, ?_⟩
  intro s hs hle
  rcases one_irreducible_subset_component π hπ hs with h | h
  · exact False.elim (oneRight_not_subset_left π hπ (hle.trans h))
  · exact h

/-- Exhaustive actual irreducible components of the same exponent-one fibre. -/
theorem one_irreducibleComponents_eq : irreducibleComponents (sourceSpecialFibre (one π hπ)) =
    {Set.range (oneLeftComponent π hπ), Set.range (oneRightComponent π hπ)} := by
  ext s
  constructor
  · intro hs
    rcases one_irreducible_subset_component π hπ hs.1 with h | h
    · exact Or.inl (Set.Subset.antisymm h (hs.2 (oneLeft_range_irreducible π hπ) h))
    · exact Or.inr (Set.Subset.antisymm h (hs.2 (oneRight_range_irreducible π hπ) h))
  · rintro (rfl | rfl)
    · exact oneLeft_mem_irreducibleComponents π hπ
    · exact oneRight_mem_irreducibleComponents π hπ

/-- Scheme-theoretic adjacent intersection and its two actual branch endpoints. -/
theorem one_intersection_isPullback :
    IsPullback (Cross.endpoint (IsLocalRing.ResidueField R)) (Cross.endpoint
      (IsLocalRing.ResidueField R))
      (oneLeftComponent π hπ) (oneRightComponent π hπ) :=
  (Cross.intersection_isPullback (IsLocalRing.ResidueField R)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (oneSpecialFibreIso π hπ).symm
    (by simp) (by simp) (by simp [oneLeftComponent]) (by simp [oneRightComponent])

/-- Identifies the residue-field point with the scheme-theoretic intersection of the two
exponent-one branches. -/
def oneIntersectionIso : Spec (.of (IsLocalRing.ResidueField R)) ≅
    pullback (oneLeftComponent π hπ) (oneRightComponent π hπ) :=
  (one_intersection_isPullback π hπ).isoPullback

@[reassoc] lemma oneIntersectionIso_hom_fst :
    (oneIntersectionIso π hπ).hom ≫ pullback.fst _ _ = Cross.endpoint _ := by
  simp [oneIntersectionIso]
@[reassoc] lemma oneIntersectionIso_hom_snd :
    (oneIntersectionIso π hπ).hom ≫ pullback.snd _ _ = Cross.endpoint _ := by
  simp [oneIntersectionIso]

@[reassoc] lemma oneLeftComponent_base_triangle :
    oneLeftComponent π hπ ≫ pullback.snd ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)[X])) := by
  rw [oneLeftComponent, Category.assoc, oneSpecialFibreIso_inv_snd]
  rw [Cross.left, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (Cross.leftHom (IsLocalRing.ResidueField R)).commutes

@[reassoc] lemma oneRightComponent_base_triangle :
    oneRightComponent π hπ ≫ pullback.snd ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom
        (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)[X])) := by
  rw [oneRightComponent, Category.assoc, oneSpecialFibreIso_inv_snd]
  rw [Cross.right, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (Cross.rightHom (IsLocalRing.ResidueField R)).commutes

/-- The actual disjoint union of the two smooth affine branches. -/
def oneSeparatedBranches : Scheme.{u} :=
  Cross.line (IsLocalRing.ResidueField R) ⨿ Cross.line (IsLocalRing.ResidueField R)

/-- Maps the disjoint union of the two affine branches into the exponent-one special fibre. -/
def oneSeparatedBranchMap : oneSeparatedBranches (R := R) ⟶ sourceSpecialFibre (one π hπ) :=
  coprod.desc (oneLeftComponent π hπ) (oneRightComponent π hπ)

instance oneSeparatedBranchMap_finite : IsFinite (oneSeparatedBranchMap π hπ) := by
  dsimp [oneSeparatedBranchMap]; infer_instance

lemma oneSeparatedBranchMap_surjective : Surjective (oneSeparatedBranchMap π hπ) := by
  constructor
  intro z
  rcases one_components_cover π hπ z with ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨(coprod.inl : Cross.line (IsLocalRing.ResidueField R) ⟶ oneSeparatedBranches (R := R))
    p, ?_⟩
    change (coprod.inl ≫ coprod.desc (oneLeftComponent π hπ) (oneRightComponent π hπ)) p = z
    rw [coprod.inl_desc]
    exact hp
  · refine ⟨(coprod.inr : Cross.line (IsLocalRing.ResidueField R) ⟶ oneSeparatedBranches (R := R))
    p, ?_⟩
    change (coprod.inr ≫ coprod.desc (oneLeftComponent π hπ) (oneRightComponent π hπ)) p = z
    rw [coprod.inr_desc]
    exact hp

/-- The endpoint in the left summand of the separated pair of affine branches. -/
def oneLeftBranch : Spec (.of (IsLocalRing.ResidueField R)) ⟶ oneSeparatedBranches (R := R) :=
  Cross.endpoint _ ≫ coprod.inl

/-- The endpoint in the right summand of the separated pair of affine branches. -/
def oneRightBranch : Spec (.of (IsLocalRing.ResidueField R)) ⟶ oneSeparatedBranches (R := R) :=
  Cross.endpoint _ ≫ coprod.inr

lemma one_branches_distinct : oneLeftBranch (R := R) ≠ oneRightBranch (R := R) := by
  intro h
  let p : Spec (.of (IsLocalRing.ResidueField R)) := ⟨⊥, inferInstance⟩
  have hp := congr($h p)
  exact Set.disjoint_left.mp (isCompl_range_inl_inr
    (Cross.line (IsLocalRing.ResidueField R)) (Cross.line (IsLocalRing.ResidueField R))).disjoint
    (show oneLeftBranch p ∈ Set.range (coprod.inl : _ ⟶ oneSeparatedBranches (R := R)) from
      ⟨Cross.endpoint _ p, rfl⟩)
    (show oneLeftBranch p ∈ Set.range (coprod.inr : _ ⟶ oneSeparatedBranches (R := R)) from
      ⟨Cross.endpoint _ p, hp.symm⟩)

@[reassoc] lemma oneLeftBranch_triangle :
    oneLeftBranch (R := R) ≫ oneSeparatedBranchMap π hπ = oneNode π hπ := by
  simp only [oneLeftBranch, oneSeparatedBranchMap, Category.assoc, coprod.inl_desc,
    oneLeftComponent_endpoint]

@[reassoc] lemma oneRightBranch_triangle :
    oneRightBranch (R := R) ≫ oneSeparatedBranchMap π hπ = oneNode π hπ := by
  simp only [oneRightBranch, oneSeparatedBranchMap, Category.assoc, coprod.inr_desc,
    oneRightComponent_endpoint]

@[reassoc] lemma zeroSpecialFibreGmIso_inv_snd :
    (zeroSpecialFibreGmIso π).inv ≫ pullback.snd ((zero π).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R)
        (Localization.Away (Polynomial.X : (IsLocalRing.ResidueField R)[X])))) := by
  rw [zeroSpecialFibreGmIso, Iso.trans_inv, Category.assoc, zeroSpecialFibreIso_inv_snd]
  change Spec.map (CommRingCat.ofHom
    (unitNodeLaurentEquiv (IsLocalRing.ResidueField R)).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (unitNodeLaurentEquiv (IsLocalRing.ResidueField R)).commutes

/-- Exhaustive fibre of the finite separated-branch map over the actual node. -/
theorem one_separated_branch_fibre (p : Spec (.of (IsLocalRing.ResidueField R)))
    (z : oneSeparatedBranches (R := R)) :
    oneSeparatedBranchMap π hπ z = oneNode π hπ p ↔
      z = oneLeftBranch p ∨ z = oneRightBranch p := by
  constructor
  · intro hz
    have hc : Set.range (coprod.inl : Cross.line (IsLocalRing.ResidueField R) ⟶
      oneSeparatedBranches (R := R)) ∪
        Set.range (coprod.inr : Cross.line (IsLocalRing.ResidueField R) ⟶ oneSeparatedBranches (R
          := R)) = Set.univ :=
      (isCompl_range_inl_inr _ _).sup_eq_top
    have hm : z ∈ Set.range (coprod.inl : _ ⟶ oneSeparatedBranches (R := R)) ∪
        Set.range (coprod.inr : _ ⟶ oneSeparatedBranches (R := R)) := by rw [hc]; trivial
    rcases hm with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · change (coprod.inl ≫ coprod.desc (oneLeftComponent π hπ) (oneRightComponent π hπ)) x = _ at hz
      rw [coprod.inl_desc] at hz
      have hn := congr($(oneLeftComponent_endpoint π hπ) p)
      have hx := (oneLeftComponent π hπ).isClosedEmbedding.injective (hz.trans hn.symm)
      exact Or.inl (congrArg (coprod.inl : _ ⟶ oneSeparatedBranches (R := R)) hx)
    · change (coprod.inr ≫ coprod.desc (oneLeftComponent π hπ) (oneRightComponent π hπ)) x = _ at hz
      rw [coprod.inr_desc] at hz
      have hn := congr($(oneRightComponent_endpoint π hπ) p)
      have hx := (oneRightComponent π hπ).isClosedEmbedding.injective (hz.trans hn.symm)
      exact Or.inr (congrArg (coprod.inr : _ ⟶ oneSeparatedBranches (R := R)) hx)
  · rintro (rfl | rfl)
    · exact congr($(oneLeftBranch_triangle π hπ) p)
    · exact congr($(oneRightBranch_triangle π hπ) p)

/-- The displayed base-case source is definitionally the actual recursive source. -/
theorem resolve_zero_specialFibre_eq
    (hex : AlgebraicGeometry.Scheme.Blowup.NoetherianBlowupExistence.{u})
    (hp : AlgebraicGeometry.Scheme.Blowup.NoetherianBlowupProper.{u})
    (ha : AlgebraicGeometry.Scheme.Blowup.BlowupAffineAtlas.{u}) :
    sourceSpecialFibre (resolve π hπ hex hp ha 0) = sourceSpecialFibre (zero π) := rfl

theorem resolve_one_specialFibre_eq
    (hex : AlgebraicGeometry.Scheme.Blowup.NoetherianBlowupExistence.{u})
    (hp : AlgebraicGeometry.Scheme.Blowup.NoetherianBlowupProper.{u})
    (ha : AlgebraicGeometry.Scheme.Blowup.BlowupAffineAtlas.{u}) :
    sourceSpecialFibre (resolve π hπ hex hp ha 1) = sourceSpecialFibre (one π hπ) := rfl

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeResolutionBaseFibres


section NodeFibreCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Pullback.Fibre
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Blowup.Coordinates
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

/-- The literal scalar fibre of either uniformizer outer chart. -/
def outerFibre : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))))
    (residueBase (R := R))

/-- The recursively resolved middle fibre as an actual open of the new fibre. -/
def middleFibreChart : sourceSpecialFibre E ⟶ sourceSpecialFibre (step B hπ E) :=
  fibreChart (stepModifiedChart B hπ E) (E.map ≫ base)
    ((step B hπ E).map ≫ base) residueBase (stepModifiedChart_base_triangle B hπ E)

/-- The left outer chart on the special fibre of a resolution step. -/
def leftFibreChart : outerFibre (π := π) ⟶ sourceSpecialFibre (step B hπ E) :=
  fibreChart (stepLeftChart B hπ E) _ _ residueBase (stepLeftChart_base_triangle B hπ E)

/-- The right outer chart on the special fibre of a resolution step. -/
def rightFibreChart : outerFibre (π := π) ⟶ sourceSpecialFibre (step B hπ E) :=
  fibreChart (stepRightChart B hπ E) _ _ residueBase (stepRightChart_base_triangle B hπ E)

instance middleFibreChart_isOpenImmersion : IsOpenImmersion (middleFibreChart B hπ E) := by
  dsimp [middleFibreChart]; infer_instance
instance leftFibreChart_isOpenImmersion : IsOpenImmersion (leftFibreChart B hπ E) := by
  dsimp [leftFibreChart]; infer_instance
instance rightFibreChart_isOpenImmersion : IsOpenImmersion (rightFibreChart B hπ E) := by
  dsimp [rightFibreChart]; infer_instance

@[reassoc] lemma middleFibreChart_source_triangle :
    middleFibreChart B hπ E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase =
      pullback.fst (E.map ≫ base) residueBase ≫ stepModifiedChart B hπ E := fibreChart_fst ..
@[reassoc] lemma leftFibreChart_source_triangle :
    leftFibreChart B hπ E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase =
      pullback.fst _ residueBase ≫ stepLeftChart B hπ E := fibreChart_fst ..
@[reassoc] lemma rightFibreChart_source_triangle :
    rightFibreChart B hπ E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase =
      pullback.fst _ residueBase ≫ stepRightChart B hπ E := fibreChart_fst ..

@[reassoc] lemma middleFibreChart_base_triangle :
    middleFibreChart B hπ E ≫ pullback.snd ((step B hπ E).map ≫ base) residueBase =
      pullback.snd (E.map ≫ base) residueBase := fibreChart_snd ..
@[reassoc] lemma leftFibreChart_base_triangle :
    leftFibreChart B hπ E ≫ pullback.snd ((step B hπ E).map ≫ base) residueBase =
      pullback.snd _ residueBase := fibreChart_snd ..
@[reassoc] lemma rightFibreChart_base_triangle :
    rightFibreChart B hπ E ≫ pullback.snd ((step B hπ E).map ≫ base) residueBase =
      pullback.snd _ residueBase := fibreChart_snd ..

lemma fibre_three_charts_cover (z : sourceSpecialFibre (step B hπ E)) :
    z ∈ Set.range (middleFibreChart B hπ E) ∨
      z ∈ Set.range (leftFibreChart B hπ E) ∨ z ∈ Set.range (rightFibreChart B hπ E) := by
  dsimp only [sourceSpecialFibre] at z ⊢
  unfold middleFibreChart leftFibreChart rightFibreChart
  dsimp only [sourceSpecialFibre, outerFibre]
  rw [fibreChart_range, fibreChart_range, fibreChart_range]
  exact step_three_charts_cover B hπ E _

/-- Exhaustive actual fibre atlas, obtained by base change of the constructed charts. -/
def fibreStepCover : (sourceSpecialFibre (step B hπ E)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 3)
    ![sourceSpecialFibre E, outerFibre (π := π), outerFibre (π := π)]
    (fun | 0 => middleFibreChart B hπ E
         | 1 => leftFibreChart B hπ E
         | 2 => rightFibreChart B hπ E)
    (by
      intro z
      rcases fibre_three_charts_cover B hπ E z with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩)
    (by intro i; fin_cases i <;> infer_instance)

/-- Each outer fibre is the literal reduced cross over the residue field. -/
def outerFibreIso : outerFibre (π := π) ≅ Cross.scheme (IsLocalRing.ResidueField R) :=
  (Scheme.PowerNode.specializationIso (S := IsLocalRing.ResidueField R) π).symm ≪≫
    nodeParameterIso (by
      simp only [IsLocalRing.ResidueField.algebraMap_eq,
        IsDiscreteValuationRing.uniformizer_residue_zero π hπ])

include hπ in
lemma outerFibre_reduced : AlgebraicGeometry.IsReduced (outerFibre (π := π)) :=
  isReduced_of_isOpenImmersion (outerFibreIso hπ).hom

lemma fibre_step_reduced [AlgebraicGeometry.IsReduced (sourceSpecialFibre E)] :
    AlgebraicGeometry.IsReduced (sourceSpecialFibre (step B hπ E)) := by
  let := outerFibre_reduced hπ
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover _ (fibreStepCover B hπ E)).mpr
  intro i
  change Fin 3 at i
  fin_cases i
  · change AlgebraicGeometry.IsReduced (sourceSpecialFibre E); infer_instance
  · change AlgebraicGeometry.IsReduced (outerFibre (π := π)); infer_instance
  · change AlgebraicGeometry.IsReduced (outerFibre (π := π)); infer_instance

variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})

/-- Every actual recursively resolved special fibre is reduced. -/
theorem resolve_specialFibre_reduced : (n : ℕ) →
    AlgebraicGeometry.IsReduced (sourceSpecialFibre (resolve π hπ hex hp ha n))
  | 0 => by
      exact isReduced_of_isOpenImmersion (zeroSpecialFibreGmIso π).hom
  | 1 => oneSpecialFibre_reduced π hπ
  | m + 2 => by
      let := resolve_specialFibre_reduced m
      exact fibre_step_reduced (OneStepBlowup.ofFamilies π m hex hp ha) hπ _

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreCharts


section NodeFibreEnds

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Pullback.Fibre
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "k" => IsLocalRing.ResidueField R

lemma residuePolynomial_coeff (r : R) :
    algebraMap R k[X] r = C (IsLocalRing.residue R r) := rfl

/-- The literal strict-transform branch coordinate maps before choosing charts. -/
def residueLeftHom (c : R) (hc : algebraMap R k c = 0) : PlaneNode.Ring c →ₐ[R] k[X] :=
  PlaneNode.lift c Polynomial.X 0 (by
    change Polynomial.X * 0 = C (algebraMap R k c)
    rw [hc, map_zero]
    simp)
/-- The residue-field branch homomorphism sending `U` to zero and `V` to the polynomial variable. -/
def residueRightHom (c : R) (hc : algebraMap R k c = 0) : PlaneNode.Ring c →ₐ[R] k[X] :=
  PlaneNode.lift c 0 Polynomial.X (by
    change 0 * Polynomial.X = C (algebraMap R k c)
    rw [hc, map_zero]
    simp)

lemma residueLeftHom_surjective (c : R) (hc : algebraMap R k c = 0) :
    Function.Surjective (residueLeftHom c hc) := by
  intro p
  have h : p ∈ (residueLeftHom c hc).range := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact (residueLeftHom c hc).range.add_mem hp hq
    | monomial n a =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
      refine ⟨algebraMap R (PlaneNode.Ring c) r * PlaneNode.U c ^ n, ?_⟩
      simp [residueLeftHom, C_mul_X_pow_eq_monomial]
  exact h

lemma residueRightHom_surjective (c : R) (hc : algebraMap R k c = 0) :
    Function.Surjective (residueRightHom c hc) := by
  intro p
  have h : p ∈ (residueRightHom c hc).range := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact (residueRightHom c hc).range.add_mem hp hq
    | monomial n a =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
      refine ⟨algebraMap R (PlaneNode.Ring c) r * PlaneNode.V c ^ n, ?_⟩
      simp [residueRightHom, C_mul_X_pow_eq_monomial]
  exact h

variable {π : R} (hπ : Irreducible π)

include hπ in
lemma residue_uniformizer : algebraMap R k π = 0 := by
  simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
    IsDiscreteValuationRing.uniformizer_residue_zero π hπ

include hπ in
lemma residue_uniformizer_pow (n : ℕ) : algebraMap R k (π^(n + 1)) = 0 := by
  rw [map_pow, residue_uniformizer hπ, zero_pow (Nat.succ_ne_zero n)]

/-- Branch projection into the actual uniformizer chart over R. -/
def outerBranchProjection : Cross.line k ⟶ Spec (.of (PlaneNode.Ring π)) :=
  Spec.map (CommRingCat.ofHom (residueLeftHom π (residue_uniformizer hπ)).toRingHom)

@[reassoc] lemma outerBranchProjection_base :
    outerBranchProjection hπ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫ residueBase := by
  rw [outerBranchProjection, Spec.map_algHom_algebraMap]
  rw [residueBase, ← Spec.map_comp]
  rfl

/-- The nonexceptional branch in either actual outer fibre chart. -/
def outerEndBranch : Cross.line k ⟶ outerFibre (π := π) :=
  pullback.lift (outerBranchProjection hπ)
    (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) (outerBranchProjection_base hπ)

@[reassoc] lemma outerEndBranch_fst :
    outerEndBranch hπ ≫ pullback.fst _ residueBase = outerBranchProjection hπ :=
  pullback.lift_fst ..
@[reassoc] lemma outerEndBranch_snd :
    outerEndBranch hπ ≫ pullback.snd _ residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := pullback.lift_snd ..

instance outerBranchProjection_closedImmersion : IsClosedImmersion (outerBranchProjection hπ) :=
  IsClosedImmersion.spec_of_surjective _ (residueLeftHom_surjective π (residue_uniformizer hπ))

instance outerEndBranch_closedImmersion : IsClosedImmersion (outerEndBranch hπ) := by
  let : IsClosedImmersion (outerEndBranch hπ ≫ pullback.fst _ residueBase) := by
    rw [outerEndBranch_fst]; infer_instance
  exact IsClosedImmersion.of_comp (outerEndBranch hπ) (pullback.fst _ residueBase)

variable {m : ℕ} (B : OneStepBlowup.Data π m) (E : Data π m)

/-- Actual two strict-transform ends; both outer charts use U for the surviving coordinate. -/
def stepLeftEnd : Cross.line k ⟶ sourceSpecialFibre (step B hπ E) :=
  outerEndBranch hπ ≫ leftFibreChart B hπ E
/-- The surviving affine end branch mapped through the right outer chart of the resolution step. -/
def stepRightEnd : Cross.line k ⟶ sourceSpecialFibre (step B hπ E) :=
  outerEndBranch hπ ≫ rightFibreChart B hπ E

@[reassoc] lemma stepLeftEnd_base :
    stepLeftEnd hπ B E ≫ pullback.snd ((step B hπ E).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  simp only [stepLeftEnd, Category.assoc, leftFibreChart_base_triangle, outerEndBranch_snd]
@[reassoc] lemma stepRightEnd_base :
    stepRightEnd hπ B E ≫ pullback.snd ((step B hπ E).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  simp only [stepRightEnd, Category.assoc, rightFibreChart_base_triangle, outerEndBranch_snd]

lemma leftBase_residueLeft :
    (residueLeftHom π (residue_uniformizer hπ)).comp (leftBase π m) =
      residueLeftHom (π^(m + 2)) (residue_uniformizer_pow hπ (m + 1)) := by
  apply PlaneNode.hom_ext <;> simp [leftBase, residueLeftHom]

lemma rightBase_residueLeft :
    (residueLeftHom π (residue_uniformizer hπ)).comp (rightBase π m) =
      residueRightHom (π^(m + 2)) (residue_uniformizer_pow hπ (m + 1)) := by
  apply PlaneNode.hom_ext <;> simp [rightBase_u, rightBase_v, residueLeftHom, residueRightHom]

@[reassoc] lemma stepLeftEnd_target_triangle :
    stepLeftEnd hπ B E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase ≫
        (step B hπ E).map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π^(m + 2)) (residue_uniformizer_pow hπ (m + 1))).toRingHom) := by
  rw [stepLeftEnd, Category.assoc, leftFibreChart_source_triangle_assoc,
    outerEndBranch_fst_assoc, stepLeftChart_triangle]
  rw [outerBranchProjection, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (leftBase_residueLeft hπ (m := m))

@[reassoc] lemma stepRightEnd_target_triangle :
    stepRightEnd hπ B E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase ≫
        (step B hπ E).map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π^(m + 2)) (residue_uniformizer_pow hπ (m + 1))).toRingHom) := by
  rw [stepRightEnd, Category.assoc, rightFibreChart_source_triangle_assoc,
    outerEndBranch_fst_assoc, stepRightChart_triangle]
  rw [outerBranchProjection, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (rightBase_residueLeft hπ (m := m))

instance stepLeftEnd_closedImmersion : IsClosedImmersion (stepLeftEnd hπ B E) := by
  let q := pullback.fst ((step B hπ E).map ≫ base) residueBase ≫ (step B hπ E).map
  let : IsClosedImmersion (stepLeftEnd hπ B E ≫ q) := by
    dsimp [q]
    rw [stepLeftEnd_target_triangle]
    exact IsClosedImmersion.spec_of_surjective _ (residueLeftHom_surjective _
      (residue_uniformizer_pow hπ (m + 1)))
  exact IsClosedImmersion.of_comp (stepLeftEnd hπ B E) q

instance stepRightEnd_closedImmersion : IsClosedImmersion (stepRightEnd hπ B E) := by
  let q := pullback.fst ((step B hπ E).map ≫ base) residueBase ≫ (step B hπ E).map
  let : IsClosedImmersion (stepRightEnd hπ B E ≫ q) := by
    dsimp [q]
    rw [stepRightEnd_target_triangle]
    exact IsClosedImmersion.spec_of_surjective _ (residueRightHom_surjective _
      (residue_uniformizer_pow hπ (m + 1)))
  exact IsClosedImmersion.of_comp (stepRightEnd hπ B E) q

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreEnds


section NodeOuterFibreGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Pullback.Fibre
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


section Coefficients
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
/-- The coefficient specialization of a plane node that preserves its `U` and `V` coordinates. -/
def nodeSpecializeAt (c : R) (d : S) (h : algebraMap R S c = d) : PlaneNode.Ring c →ₐ[R]
  PlaneNode.Ring d :=
  PlaneNode.lift c (PlaneNode.U d) (PlaneNode.V d) (by
    rw [PlaneNode.relation, IsScalarTower.algebraMap_apply R S (PlaneNode.Ring d), h])

end Coefficients

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

/-- A coordinate-preserving cross identification retaining explicit ring maps. -/
def outerCrossIso : Cross.scheme k ≅ outerFibre (π := π) :=
  Scheme.Spec.mapIso (PlaneNode.congr (residue_uniformizer hπ)).toRingEquiv.toCommRingCatIso.op ≪≫
    Scheme.PowerNode.specializationIso (S := k) π

@[reassoc] lemma outerCrossIso_hom_fst :
    (outerCrossIso hπ).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) (residueBase
        (R := R)) =
      Spec.map (CommRingCat.ofHom (nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).toRingHom)
        := by
  rw [outerCrossIso, Iso.trans_hom, Category.assoc]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr (residue_uniformizer hπ)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) π).hom ≫ pullback.fst _ _ = _
  rw [Scheme.PowerNode.specializationIso_hom_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : ((PlaneNode.congr (residue_uniformizer hπ)).toAlgHom.restrictScalars R).comp
      (PlaneNode.coefficientMap (S := k) π) = nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)
        := by
    apply PlaneNode.hom_ext
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_U,
        nodeSpecializeAt, PlaneNode.lift_U]
      change PlaneNode.congr (residue_uniformizer hπ)
        (PlaneNode.U (algebraMap R k π)) = PlaneNode.U (0 : k)
      exact PlaneNode.congr_U _
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_V,
        nodeSpecializeAt, PlaneNode.lift_V]
      change PlaneNode.congr (residue_uniformizer hπ)
        (PlaneNode.V (algebraMap R k π)) = PlaneNode.V (0 : k)
      exact PlaneNode.congr_V _
  exact congrArg AlgHom.toRingHom h

@[reassoc] lemma outerCrossIso_hom_snd :
    (outerCrossIso hπ).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) (residueBase
        (R := R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Cross.ring k))) := by
  rw [outerCrossIso, Iso.trans_hom, Category.assoc]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr (residue_uniformizer hπ)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) π).hom ≫ pullback.snd _ _ = _
  rw [Scheme.PowerNode.specializationIso_hom_snd]
  exact Spec.map_algHom_algebraMap (PlaneNode.congr (residue_uniformizer hπ)).toAlgHom

/-- The exceptional affine branch in a single outer chart, before compactification. -/
def outerExceptionalBranch : Cross.line k ⟶ outerFibre (π := π) :=
  Cross.right k ≫ (outerCrossIso hπ).hom

/-- The origin of the residue-field cross transported into the outer node fibre. -/
def outerNode : Spec (.of k) ⟶ outerFibre (π := π) :=
  Cross.origin k ≫ (outerCrossIso hπ).hom

lemma outerEndBranch_eq : outerEndBranch hπ = Cross.left k ≫ (outerCrossIso hπ).hom := by
  apply pullback.hom_ext
  · rw [outerEndBranch_fst, Category.assoc, outerCrossIso_hom_fst]
    rw [Cross.left, outerBranchProjection, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    have h : ((Cross.leftHom k).restrictScalars R).comp
        (nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)) =
          residueLeftHom π (residue_uniformizer hπ) := by
      apply PlaneNode.hom_ext <;> simp [nodeSpecializeAt, Cross.leftHom, residueLeftHom]
    exact (congrArg AlgHom.toRingHom h).symm
  · rw [outerEndBranch_snd, Category.assoc, outerCrossIso_hom_snd]
    exact (Spec.map_algHom_algebraMap (Cross.leftHom k)).symm

instance outerExceptionalBranch_closedImmersion :
    IsClosedImmersion (outerExceptionalBranch hπ) := by
  dsimp [outerExceptionalBranch]; infer_instance

@[reassoc] lemma outerExceptionalBranch_fst :
    outerExceptionalBranch hπ ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R
      (PlaneNode.Ring π)))) (residueBase (R := R)) =
      Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) := by
  rw [outerExceptionalBranch, Category.assoc, outerCrossIso_hom_fst, Cross.right, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : ((Cross.rightHom k).restrictScalars R).comp
      (nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)) =
        residueRightHom π (residue_uniformizer hπ) := by
    apply PlaneNode.hom_ext <;> simp [nodeSpecializeAt, Cross.rightHom, residueRightHom]
  exact congrArg AlgHom.toRingHom h

@[reassoc] lemma outerExceptionalBranch_snd :
    outerExceptionalBranch hπ ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R
      (PlaneNode.Ring π)))) (residueBase (R := R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  rw [outerExceptionalBranch, Category.assoc, outerCrossIso_hom_snd]
  exact Spec.map_algHom_algebraMap (Cross.rightHom k)

@[reassoc] lemma outerEndBranch_endpoint :
    Cross.endpoint k ≫ outerEndBranch hπ = outerNode hπ := by
  rw [outerEndBranch_eq, ← Category.assoc, Cross.left_endpoint, outerNode]
@[reassoc] lemma outerExceptionalBranch_endpoint :
    Cross.endpoint k ≫ outerExceptionalBranch hπ = outerNode hπ := by
  rw [outerExceptionalBranch, ← Category.assoc, Cross.right_endpoint, outerNode]

lemma outer_branches_cover (z : outerFibre (π := π)) :
    z ∈ Set.range (outerEndBranch hπ) ∨ z ∈ Set.range (outerExceptionalBranch hπ) := by
  rw [outerEndBranch_eq]
  exact cover_postcompose (Cross.left k) (Cross.right k) (outerCrossIso hπ).hom
    (outerCrossIso hπ).hom.surjective (Cross.components_cover k) z

/-- Scheme-theoretic local intersection of the strict-transform end and exceptional branch. -/
lemma outer_branches_isPullback :
    IsPullback (Cross.endpoint k) (Cross.endpoint k)
      (outerEndBranch hπ) (outerExceptionalBranch hπ) := by
  rw [outerEndBranch_eq]
  exact (Cross.intersection_isPullback k).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (outerCrossIso hπ)
    (by simp) (by simp) (by simp) (by simp [outerExceptionalBranch])

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeOuterFibreGeometry


section NodeExplicitTransitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Pullback.Fibre
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R]

/-- Cancellation of the middle blowdown in a target where pi is nonzero.
This identifies actual atlas transitions with the explicit reciprocal formulas. -/
lemma middleBase_cancel {T : Type u} [CommRing T] [IsDomain T] [Algebra R T]
    (π : R) (m : ℕ) (hπT : algebraMap R T π ≠ 0)
    (f : PlaneNode.Ring (π ^ m) →+* T) (g : PlaneNode.Ring (π ^ m) →ₐ[R] T)
    (h : f.comp (middleBase π m).toRingHom = g.toRingHom.comp (middleBase π m).toRingHom) :
    f = g.toRingHom := by
  have hf (r : R) : f (algebraMap R (PlaneNode.Ring (π ^ m)) r) = algebraMap R T r := by
    have hr := DFunLike.congr_fun h (algebraMap R (PlaneNode.Ring (π^(m + 2))) r)
    simpa only [RingHom.comp_apply, AlgHom.commutes, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using hr
  let f' : PlaneNode.Ring (π ^ m) →ₐ[R] T := { f with commutes' := hf }
  suffices f' = g from congrArg AlgHom.toRingHom this
  apply PlaneNode.hom_ext
  · apply mul_left_cancel₀ hπT
    change algebraMap R T π * f (PlaneNode.U (π ^ m)) = algebraMap R T π * g (PlaneNode.U (π ^ m))
    have hu := DFunLike.congr_fun h (PlaneNode.U (π^(m + 2)))
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      middleBase, PlaneNode.lift_U, map_mul, hf, AlgHom.commutes, f'] using hu
  · apply mul_left_cancel₀ hπT
    change algebraMap R T π * f (PlaneNode.V (π ^ m)) = algebraMap R T π * g (PlaneNode.V (π ^ m))
    have hv := DFunLike.congr_fun h (PlaneNode.V (π^(m + 2)))
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      middleBase, PlaneNode.lift_V, map_mul, hf, AlgHom.commutes, f'] using hv

lemma spec_middleBase_cancel {T : Type u} [CommRing T] [IsDomain T] [Algebra R T]
    (π : R) (m : ℕ) (hπT : algebraMap R T π ≠ 0)
    (f : Spec (.of T) ⟶ Spec (.of (PlaneNode.Ring (π ^ m)))) (g : PlaneNode.Ring (π ^ m) →ₐ[R] T)
    (h : f ≫ Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom)) :
    f = Spec.map (CommRingCat.ofHom g.toRingHom) := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hh := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hf := middleBase_cancel π m hπT f.hom g hh
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hf

variable [IsDomain R] [hDVR : IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π) {m : ℕ}
  (B : OneStepBlowup.Data π m)

omit hDVR in
lemma nodeV_ne_zero {R : Type u} [CommRing R] [IsDomain R] (c : R) : PlaneNode.V c ≠ 0 := by
  intro h
  have h' := congrArg (nodeSwap c) h
  simpa using (nodeU_ne_zero c) (by simpa using h')

include hπ in
lemma leftOverlap_domain : IsDomain (leftOverlap π) := by
  let := node_isDomain π hπ.ne_zero
  exact Localization.Away.isDomain (nodeV_ne_zero π)

include hπ in
lemma leftOverlap_pi_ne_zero : algebraMap R (leftOverlap π) π ≠ 0 := by
  have hi := (node_away_injective π hπ.ne_zero (PlaneNode.V π) (nodeV_ne_zero π)).comp
    (node_algebraMap_injective π)
  have h := hi.ne hπ.ne_zero
  simpa only [Function.comp_apply, map_zero, ← IsScalarTower.algebraMap_apply] using h

/-- Exact old-middle coordinates on the left overlap of the actual blowup. -/
@[reassoc] lemma leftMiddleIso_explicit :
    (leftMiddleIso hπ B.atlas).hom ≫ awayMap (PlaneNode.U (π ^ m)) =
      Spec.map (CommRingCat.ofHom (middleLeftOverlapBase π m).toRingHom) := by
  let := leftOverlap_domain hπ
  apply spec_middleBase_cancel π m (leftOverlap_pi_ne_zero hπ)
  have h := leftMiddleIso_hom_triangle_assoc hπ B.atlas B.blowup.map
  rw [middleChartMap_triangle, leftChartMap_triangle] at h
  rw [Category.assoc, h]
  rw [awayMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have ht : (middleLeftOverlapBase π m).comp (middleBase π m) =
      (IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)).comp (leftBase π m) := by
    apply PlaneNode.hom_ext
    · simp [middleLeftOverlapBase, middleBase, leftBase, node_awayV_u]
    · simp only [AlgHom.comp_apply, middleBase, leftBase, PlaneNode.lift_V, map_mul,
        AlgHom.commutes, middleLeftOverlapBase]
      simp only [IsScalarTower.toAlgHom_apply]
      rw [← mul_assoc, ← map_mul, ← pow_succ']
  exact (congrArg AlgHom.toRingHom ht).symm

/-- Explicit reciprocal left transition as a triangle in the same actual blowup. -/
@[reassoc] lemma leftMiddle_explicit_triangle :
    Spec.map (CommRingCat.ofHom (middleLeftOverlapBase π m).toRingHom) ≫
        middleChartMap B.atlas hπ = awayMap (PlaneNode.V π) ≫ leftChartMap B.atlas hπ := by
  rw [← leftMiddleIso_explicit hπ B, Category.assoc]
  exact leftMiddleIso_hom_triangle hπ B.atlas

/-- Reciprocal right overlap coordinates, with the old node coordinates exchanged. -/
def middleRightOverlapBase (π : R) (m : ℕ) : PlaneNode.Ring (π ^ m) →ₐ[R] leftOverlap π :=
  (middleLeftOverlapBase π m).comp (nodeSwap (π ^ m))

@[reassoc] lemma rightMiddleIso_explicit :
    (rightMiddleIso hπ B.atlas).hom ≫ awayMap (PlaneNode.V (π ^ m)) =
      Spec.map (CommRingCat.ofHom (middleRightOverlapBase π m).toRingHom) := by
  let := leftOverlap_domain hπ
  apply spec_middleBase_cancel π m (leftOverlap_pi_ne_zero hπ)
  have h := rightMiddleIso_hom_triangle_assoc hπ B.atlas B.blowup.map
  rw [middleChartMap_triangle, rightChartMap_triangle] at h
  rw [Category.assoc, h]
  rw [awayMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have ht : (middleRightOverlapBase π m).comp (middleBase π m) =
      (IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)).comp (rightBase π m) := by
    apply PlaneNode.hom_ext
    · simp only [AlgHom.comp_apply, middleBase, PlaneNode.lift_U, map_mul, AlgHom.commutes,
        middleRightOverlapBase, nodeSwap_u, middleLeftOverlapBase, PlaneNode.lift_V,
        IsScalarTower.toAlgHom_apply, rightBase_u]
      rw [← mul_assoc, ← map_mul, ← pow_succ']
    · simp [middleRightOverlapBase, middleLeftOverlapBase, middleBase, rightBase_v,
        node_awayV_u]
  exact (congrArg AlgHom.toRingHom ht).symm

@[reassoc] lemma rightMiddle_explicit_triangle :
    Spec.map (CommRingCat.ofHom (middleRightOverlapBase π m).toRingHom) ≫
        middleChartMap B.atlas hπ = awayMap (PlaneNode.V π) ≫ rightChartMap B.atlas hπ := by
  rw [← rightMiddleIso_explicit hπ B, Category.assoc]
  exact rightMiddleIso_hom_triangle hπ B.atlas

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExplicitTransitions
