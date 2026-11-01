/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Ample
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing

/-!
# The original projective map from a nonvanishing cover

A family of actual global sections covering the scheme by their nonvanishing
opens supplies the existing section-frame constructor. Its projective map
and O(1) comparison retain the original line bundle and sections. Compactness
extracts finite coordinates. No independent projective presentation is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

variable {X : Scheme.{u}} {I : Type u}

/-- The native compatible section family of an original global section. -/
def globalSectionFamily (M : X.Modules) (s : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map (homOfLE le_top).op s) (by
      intro V W f
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

/-- Evaluation of that same family is the original restriction map. -/
theorem globalSectionFamily_val (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) :
    (globalSectionFamily M s).val (op U) = M.val.map (homOfLE le_top).op s := rfl

/-- An original nonvanishing cover gives a local unit coefficient at every
point, without assuming a separately supplied generating morphism. -/
theorem exists_unit_coefficient_of_nonvanishing_cover
    (L : LineBundle X) (s : I → Γ(L.val, ⊤))
    (hcover : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s i)) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (i : I),
      IsUnit (chartSectionEquiv X L.val U e U le_rfl
        ((globalSectionFamily L.val (s i)).val (op U))) := by
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨V, hxV, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  let c := chartSectionEquiv X L.val V e V le_rfl
    ((globalSectionFamily L.val (s i)).val (op V))
  let W := X.basicOpen c
  have hxW : x ∈ W := by
    change x ∈ X.basicOpen (chartSectionEquiv X L.val V e V le_rfl
      (L.val.val.map (homOfLE le_top).op (s i)))
    rw [← inter_nonvanishingOpen L (s i) V e]
    exact ⟨hxV, hxi⟩
  have hWV : W ≤ V := X.basicOpen_le c
  let eW := restrictOverUnitIso X L.val (homOfLE hWV) e
  refine ⟨W, hxW, eW, i, ?_⟩
  change IsUnit (chartSectionEquiv X L.val V e W hWV
    ((globalSectionFamily L.val (s i)).val (op W)))
  have hc : chartSectionEquiv X L.val V e W hWV
      ((globalSectionFamily L.val (s i)).val (op W)) = sectionRestrict X hWV c := by
    let q : Over.mk (homOfLE hWV) ⟶ Over.mk (homOfLE (show V ≤ V from le_rfl)) :=
      Over.homMk (homOfLE hWV)
    have h := PresheafOfModules.naturality_apply e.hom.val q.op
      ((globalSectionFamily L.val (s i)).val (op V))
    change chartSectionEquiv X L.val V e W hWV
      (L.val.val.map (homOfLE hWV).op ((globalSectionFamily L.val (s i)).val (op V))) =
        sectionRestrict X hWV c at h
    rw [PresheafOfModules.sections_property] at h
    exact h
  rw [hc]
  exact X.toRingedSpace.isUnit_res_basicOpen c

/-- The same original section family supplies actual normalized frames. -/
def framesOfNonvanishingCover (L : LineBundle X) (s : I → Γ(L.val, ⊤))
    (hcover : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s i)) :
    SectionFrames L.val (fun i => globalSectionFamily L.val (s i)) := by
  classical
  choose U hx e i hi using exists_unit_coefficient_of_nonvanishing_cover L s hcover
  exact {
    K := X
    U := U
    covers := eq_top_iff.mpr (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
    coordinate := i
    frame := fun x => normalizedFrame L.val (U x) (e x)
      (globalSectionFamily L.val (s (i x))) (hi x)
    selected := fun x => normalizedFrame_coefficient L.val (U x) (e x)
      (globalSectionFamily L.val (s (i x))) (hi x) }

/-- The chosen frames compute the original intrinsic nonvanishing opens. -/
theorem framesOfNonvanishingCover_nonvanishingOpen (L : LineBundle X)
    (s : I → Γ(L.val, ⊤)) (hcover : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s i)) (i : I) :
    (framesOfNonvanishingCover L s hcover).nonvanishingOpen i = nonvanishingOpen L (s i) := by
  let F := framesOfNonvanishingCover L s hcover
  calc
    F.nonvanishingOpen i = ⨆ k, F.U k ⊓ nonvanishingOpen L (s i) := by
      unfold SectionFrames.nonvanishingOpen
      apply iSup_congr
      intro k
      exact (inter_nonvanishingOpen L (s i) (F.U k) (F.frame k)).symm
    _ = (⨆ k, F.U k) ⊓ nonvanishingOpen L (s i) := by rw [iSup_inf_eq]
    _ = nonvanishingOpen L (s i) := by rw [F.covers, top_inf_eq]

/-- Compactness extracts finite coordinates from an original nonvanishing
cover, with the actual native projective map and O(1) pullback comparison. -/
theorem exists_projectiveMap_of_nonvanishing_cover
    {R : Type u} [CommRing R] [CompactSpace X]
    (p : X ⟶ Spec (.of R)) (L : LineBundle X)
    (s : I → Γ(L.val, ⊤)) (hcover : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s i)) :
    ∃ (J : Type u) (_ : Finite J) (f : X ⟶ ProjectiveSpace R J),
      f ≫ toSpec R J = p ∧
        Nonempty ((Scheme.Modules.pullback f).obj (twistingSheaf R J 1) ≅ L.val) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (nonvanishingOpen L (s i) : Set X)) (fun i => (nonvanishingOpen L (s i)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr (hcover x))
  let J := {i : I // i ∈ t}
  let s' : J → Γ(L.val, ⊤) := fun i => s i.1
  have h' : ∀ x : X, ∃ i, x ∈ nonvanishingOpen L (s' i) := by
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  let F := framesOfNonvanishingCover L s' h'
  exact ⟨J, inferInstance, F.map p, F.map_toSpec p, ⟨F.twistingPullbackIso p⟩⟩

/-- A finite original projective map with its actual O(1) comparison makes
the same original line bundle ample. -/
theorem isAmple_of_isFinite_projectiveMap {R : Type u} [CommRing R] [Finite I]
    (L : LineBundle X) (f : X ⟶ ProjectiveSpace R I) [IsFinite f]
    (e : (Scheme.Modules.pullback f).obj (twistingSheaf R I 1) ≅ L.val) : L.IsAmple :=
  ((twistingLineBundle_one_isAmple R I).pullback_of_isAffineHom f).of_iso e

end AlgebraicGeometry.ProjectiveSpace.FromSections
